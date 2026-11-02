// server.js: serves the app (web/) and its API.
// Usage: node web/server.js   (then open http://localhost:8765)
//
// API (JSON in, JSON out):
//   GET  /api/status                 -> {llm: bool}
//   POST /api/possible {rules}       -> {possible: [bool x 3]} (proven: can any call be answered?)
//   POST /api/session  {rules}       -> {exchanges: [...]} (proof first, then LLM calls through the proven gate)
//   POST /api/grade    {rules, exchanges:[{call, played}]} -> {results: [[bool...] x 3]}
// Every decision comes from the Lean program (lean.js). The LLM only proposes.
// localhost counts as a secure context, so getUserMedia (mic access) works.
// PORT env var overrides the port.

import "./env.js"; // must be first: loads .env (API key) before other modules read it
import http from "node:http";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

import { LeanBridge } from "./lean.js";
import { proposeCalls, llmConfigured } from "./llm.js";
import { answerIdeas, byTaste } from "./callgen.js";
import { CHORDS, CHORD_PCS, EXCHANGES } from "./rules.js";

const ROOT = path.dirname(fileURLToPath(import.meta.url));
const lean = new LeanBridge();
const PORT = Number(process.env.PORT) || 8765;
const HOST = "127.0.0.1"; // loopback only: don't expose the mic page on the LAN

const MIME = {
  ".html": "text/html; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
  ".mjs": "text/javascript; charset=utf-8",
  ".css": "text/css; charset=utf-8",
  ".json": "application/json; charset=utf-8",
  ".md": "text/markdown; charset=utf-8",
  ".svg": "image/svg+xml",
  ".png": "image/png",
  ".ico": "image/x-icon",
  ".wav": "audio/wav",
  ".mp3": "audio/mpeg",
  ".m4a": "audio/mp4",
};

// ---------------------------------------------------------------------------
// API

function readJson(req) {
  return new Promise((resolve, reject) => {
    let body = "";
    req.setEncoding("utf8");
    req.on("data", (c) => {
      body += c;
      if (body.length > 2e7) reject(new Error("request too large"));
    });
    req.on("end", () => {
      try { resolve(JSON.parse(body || "{}")); } catch (e) { reject(e); }
    });
  });
}

function sendJson(res, status, obj) {
  const body = JSON.stringify(obj);
  res.writeHead(status, { "Content-Type": "application/json; charset=utf-8", "Cache-Control": "no-store" }).end(body);
}

/** Can any call be answered here? Proven sound and complete in Lean
 * (`findCall`). When yes, Lean also gives a call and an answer to it. */
const possible = (exchange, rules) => lean.request({ op: "possible", exchange, rules });

/** Gate Claude's calls for one exchange: the proven gate picks the first one
 * that can be answered (most lick-like first; order only). */
async function gateClaude(exchange, rules, candidates) {
  const calls = byTaste(candidates ?? []);
  if (!calls.length) return { chosen: null, rejected: 0 };
  const r = await lean.request({ op: "gate", exchange, rules, proposals: calls });
  return r.chosen === null ? { chosen: null, rejected: calls.length } : { chosen: calls[r.chosen], hint: r.hint, rejected: r.chosen };
}

/** A musical answer that keeps every rule: the first idea the Lean grader
 * passes on all rules. Falls back to the search's own answer, which is
 * proven to keep the rules but may sound odd. */
async function musicalAnswer(exchange, rules, call, fallback) {
  const chordPcs = EXCHANGES[exchange].answerBars.map((b) => CHORD_PCS[CHORDS[b - 1]]);
  const ideas = answerIdeas(call, exchange + 1, chordPcs);
  for (let i = 0; i < ideas.length; i += 40) {
    const batch = ideas.slice(i, i + 40);
    const r = await lean.request({ op: "gradeMany", exchange, rules, call, answers: batch });
    if (r.first !== null) return batch[r.first];
  }
  return fallback;
}

// Debug recordings (local only): web/debug/<id>.json and <id>.wav
const DEBUG_DIR = path.join(ROOT, "debug");

function wavFromPcm16(pcm, rate) {
  const h = Buffer.alloc(44);
  h.write("RIFF", 0); h.writeUInt32LE(36 + pcm.length, 4); h.write("WAVE", 8);
  h.write("fmt ", 12); h.writeUInt32LE(16, 16); h.writeUInt16LE(1, 20); h.writeUInt16LE(1, 22);
  h.writeUInt32LE(rate, 24); h.writeUInt32LE(rate * 2, 28); h.writeUInt16LE(2, 32); h.writeUInt16LE(16, 34);
  h.write("data", 36); h.writeUInt32LE(pcm.length, 40);
  return Buffer.concat([h, pcm]);
}

function readRaw(req, limit = 64e6) {
  return new Promise((resolve, reject) => {
    const parts = [];
    let n = 0;
    req.on("data", (c) => { n += c.length; if (n > limit) reject(new Error("too large")); else parts.push(c); });
    req.on("end", () => resolve(Buffer.concat(parts)));
  });
}

async function api(req, res, urlPath) {
  if (urlPath === "/api/debug/audio" && req.method === "POST") {
    const q = new URL(req.url, "http://x").searchParams;
    const id = String(q.get("id") || "").replace(/[^0-9a-z-]/gi, "");
    const rate = Number(q.get("rate")) || 48000;
    if (!id) return sendJson(res, 400, { error: "missing id" });
    fs.mkdirSync(DEBUG_DIR, { recursive: true });
    fs.writeFileSync(path.join(DEBUG_DIR, `${id}.wav`), wavFromPcm16(await readRaw(req), rate));
    return sendJson(res, 200, { ok: true });
  }
  if (urlPath === "/api/status") return sendJson(res, 200, { llm: llmConfigured() });
  if (req.method !== "POST") return sendJson(res, 405, { error: "use POST" });
  const body = await readJson(req);
  const rules = Array.isArray(body.rules) ? body.rules : [];

  if (urlPath === "/api/debug/meta") {
    const id = new Date().toISOString().replace(/[:.]/g, "-");
    fs.mkdirSync(DEBUG_DIR, { recursive: true });
    fs.writeFileSync(path.join(DEBUG_DIR, `${id}.json`), JSON.stringify(body, null, 1));
    console.log(`debug: saved session ${id}`);
    return sendJson(res, 200, { id });
  }

  if (urlPath === "/api/possible") {
    const out = [];
    for (const e of [0, 1, 2]) out.push((await possible(e, rules)).possible);
    return sendJson(res, 200, { possible: out });
  }

  if (urlPath === "/api/session") {
    // 1. Proof first: for each exchange, can any call be answered at all?
    const proofs = [];
    for (const e of [0, 1, 2]) proofs.push(await possible(e, rules));
    const exchanges = proofs.map((p, e) => ({ exchange: e, possible: p.possible, call: null, hint: null, source: null, claudeRejected: 0 }));
    if (proofs.some((p) => !p.possible)) return sendJson(res, 200, { exchanges, llm: llmConfigured(), llmError: null });

    // 2. Claude writes calls; the proven gate keeps one it can answer. If none
    //    of Claude's calls can be answered, ask once more.
    let llmError = null;
    const ask = async () => {
      if (!llmConfigured()) return [[], [], []];
      try { return await proposeCalls(rules); } catch (e) {
        llmError = String(e.message || e);
        console.warn(`LLM failed: ${llmError}`);
        return [[], [], []];
      }
    };
    for (let attempt = 0; attempt < 2 && exchanges.some((x) => !x.call); attempt++) {
      if (attempt > 0 && llmError) break;
      const llmCalls = await ask();
      for (const x of exchanges) {
        if (x.call) continue;
        const g = await gateClaude(x.exchange, rules, llmCalls[x.exchange]);
        x.claudeRejected += g.rejected;
        if (g.chosen) Object.assign(x, { call: g.chosen, hint: g.hint, source: "claude" });
      }
    }
    // 3. Still nothing from Claude: play the call the proof itself found.
    for (const x of exchanges) {
      if (!x.call) Object.assign(x, { call: proofs[x.exchange].call, hint: proofs[x.exchange].answer, source: "proof" });
      x.hint = await musicalAnswer(x.exchange, rules, x.call, x.hint);
    }
    return sendJson(res, 200, { exchanges, llm: llmConfigured(), llmError });
  }

  if (urlPath === "/api/grade") {
    const results = [];
    for (const [e, x] of (body.exchanges ?? []).entries()) {
      if (!x?.call || !x?.played) { results.push(null); continue; }
      const r = await lean.request({ op: "grade", exchange: e, rules, call: x.call, played: x.played });
      results.push(r.results);
    }
    return sendJson(res, 200, { results });
  }
  return sendJson(res, 404, { error: "unknown API route" });
}

// ---------------------------------------------------------------------------
// Static files + routing

const server = http.createServer((req, res) => {
  const pathOnly = (req.url || "/").split("?")[0];
  if (pathOnly.startsWith("/api/")) {
    api(req, res, pathOnly).catch((e) => {
      console.error(e);
      sendJson(res, 500, { error: String(e.message || e) });
    });
    return;
  }
  if (req.method !== "GET" && req.method !== "HEAD") {
    res.writeHead(405, { Allow: "GET, HEAD" }).end("Method not allowed");
    return;
  }
  let urlPath;
  try {
    urlPath = decodeURIComponent(new URL(req.url, "http://x").pathname);
  } catch {
    res.writeHead(400).end("Bad request");
    return;
  }
  if (urlPath.endsWith("/")) urlPath += "index.html";
  // Resolve inside ROOT and refuse anything that escapes it (path traversal).
  const filePath = path.join(ROOT, path.normalize(urlPath));
  if (filePath !== ROOT && !filePath.startsWith(ROOT + path.sep)) {
    res.writeHead(403).end("Forbidden");
    return;
  }
  fs.stat(filePath, (err, st) => {
    if (err || !st.isFile()) {
      res.writeHead(404, { "Content-Type": "text/plain" }).end("Not found");
      return;
    }
    res.writeHead(200, {
      "Content-Type": MIME[path.extname(filePath).toLowerCase()] ?? "application/octet-stream",
      "Content-Length": st.size,
      "Cache-Control": "no-store", // always serve fresh files during the hackathon
    });
    if (req.method === "HEAD") return res.end();
    fs.createReadStream(filePath).pipe(res);
  });
});

lean.start(); // fail fast if the Lean program is missing
server.listen(PORT, HOST, () => {
  console.log(`Serving ${ROOT}`);
  console.log(llmConfigured() ? `LLM: Claude` : `LLM: not configured (set ANTHROPIC_API_KEY); using the calls the proof finds`);
  console.log(`Open http://localhost:${PORT}`);
});
