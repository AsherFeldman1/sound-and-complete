// lean.js: talk to the proven Lean core (`sound-and-complete serve`).
//
// The Lean program reads one JSON request per line and writes one JSON reply
// per line, in order. We keep one process alive and queue requests so replies
// match requests. If the process dies, the next request restarts it.

import { spawn } from "node:child_process";
import path from "node:path";
import fs from "node:fs";
import { fileURLToPath } from "node:url";

const REPO = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const BIN = path.join(REPO, ".lake", "build", "bin", process.platform === "win32" ? "sound-and-complete.exe" : "sound-and-complete");

export class LeanBridge {
  constructor(bin = BIN) {
    this.bin = bin;
    this.proc = null;
    this.buf = "";
    this.waiting = []; // FIFO of {resolve, reject}
    this.chain = Promise.resolve();
  }

  start() {
    if (!fs.existsSync(this.bin)) {
      throw new Error(`Lean program not found at ${this.bin}. Run \`make install\` (or \`lake build\`) first.`);
    }
    this.proc = spawn(this.bin, ["serve"], { stdio: ["pipe", "pipe", "inherit"] });
    this.buf = "";
    this.proc.stdout.setEncoding("utf8");
    this.proc.stdout.on("data", (chunk) => {
      this.buf += chunk;
      let nl;
      while ((nl = this.buf.indexOf("\n")) >= 0) {
        const line = this.buf.slice(0, nl);
        this.buf = this.buf.slice(nl + 1);
        const w = this.waiting.shift();
        if (!w) continue;
        try {
          const reply = JSON.parse(line);
          if (reply.error) w.reject(new Error(`Lean: ${reply.error}`));
          else w.resolve(reply);
        } catch (e) {
          w.reject(e);
        }
      }
    });
    this.proc.on("exit", (code) => {
      for (const w of this.waiting.splice(0)) w.reject(new Error(`Lean process exited (${code})`));
      this.proc = null;
    });
  }

  /** Send one request; resolves with the parsed reply. Requests run one at a time. */
  request(obj) {
    const run = () =>
      new Promise((resolve, reject) => {
        if (!this.proc) this.start();
        this.waiting.push({ resolve, reject });
        this.proc.stdin.write(JSON.stringify(obj) + "\n");
      });
    const p = this.chain.then(run, run);
    this.chain = p.catch(() => {});
    return p;
  }

  stop() {
    this.proc?.kill();
  }
}
