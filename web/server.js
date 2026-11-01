// server.js: serves the app (web/) and its API.
// Usage: node web/server.js   (then open http://localhost:8765)
//
// API (JSON in, JSON out):
//   GET  /api/status                 -> {llm: bool}
//   POST /api/conflict {rules}       -> {conflict}        (proven warning)
//   POST /api/session  {rules}       -> {exchanges: [...]} (LLM calls, proven gate, hint)
//   POST /api/grade    {rules, exchanges:[{call, played}]} -> {results: [[bool...] x 3]}
// Every decision comes from the Lean program (lean.js). The LLM only proposes.
// localhost counts as a secure context, so getUserMedia (mic access) works.
// PORT env var overrides the port.

import http from "node:http";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

import { LeanBridge } from "./lean.js";
import { proposeCalls, llmConfigured } from "./llm.js";
import { generateCalls, answerIdeas } from "./callgen.js";
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

/** Gate one exchange: try the candidates in order, the proven gate picks. */
async function gateExchange(exchange, rules, llmCandidates) {
  const tries = [
    { source: "claude", calls: llmCandidates },
    { source: "built-in", calls: generateCalls(8) },
    { source: "built-in", calls: generateCalls(32) },
  ];
  const rejected = [];
  for (const { source, calls } of tries) {
    if (!calls.length) continue;
    const r = await lean.request({ op: "gate", exchange, rules, proposals: calls });
    if (r.chosen !== null) {
      rejected.push(...calls.slice(0, r.chosen).map((c) => ({ source, call: c })));
      const call = calls[r.chosen];
      return { exchange, call, hint: await musicalAnswer(exchange, rules, call, r.hint), source, rejected };
    }
    rejected.push(...calls.map((c) => ({ source, call: c })));
  }
  return { exchange, call: null, hint: null, source: null, rejected };
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

  if (urlPath === "/api/conflict") {
    const r = await lean.request({ op: "conflict", exchange: 0, rules });
    // The warning can depend on the exchange (turnaround rules): check all three.
    let conflict = r.conflict;
    for (const e of [1, 2]) conflict ||= (await lean.request({ op: "conflict", exchange: e, rules })).conflict;
    return sendJson(res, 200, { conflict });
  }

  if (urlPath === "/api/session") {
    let llmCalls = [[], [], []];
    let llmError = null;
    if (llmConfigured()) {
      try {
        llmCalls = await proposeCalls(rules);
      } catch (e) {
        llmError = String(e.message || e);
        console.warn(`LLM failed, using built-in calls: ${llmError}`);
      }
    }
    const exchanges = [];
    for (const e of [0, 1, 2]) exchanges.push(await gateExchange(e, rules, llmCalls[e]));
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
  console.log(llmConfigured() ? `LLM: Claude` : `LLM: not configured (set ANTHROPIC_API_KEY); using built-in calls`);
  console.log(`Open http://localhost:${PORT}`);
});
