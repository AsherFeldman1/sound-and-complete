// Download the band's recorded instruments into web/samples/ (run by `make install`).
// The list of files lives in ../audio/sounds.js. Files already present are skipped.
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { SOUND_OPTIONS } from "../audio/sounds.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const files = Object.values(SOUND_OPTIONS).flat().flatMap((o) => o.files);
const todo = files.filter((f) => !fs.existsSync(path.join(here, f.path)));
let failed = 0;
async function get(f) {
  for (let attempt = 1; attempt <= 3; attempt++) {
    try {
      const res = await fetch(f.url);
      if (!res.ok) throw new Error(`HTTP ${res.status}`);
      const out = path.join(here, f.path);
      fs.mkdirSync(path.dirname(out), { recursive: true });
      fs.writeFileSync(out, Buffer.from(await res.arrayBuffer()));
      return;
    } catch (e) {
      if (attempt === 3) { failed++; console.error(`failed: ${f.url} (${e.message})`); }
    }
  }
}
const queue = [...todo];
await Promise.all(Array.from({ length: 12 }, async () => { while (queue.length) await get(queue.shift()); }));
console.log(`samples: ${files.length - todo.length} already here, ${todo.length - failed} downloaded, ${failed} failed`);
if (failed) process.exit(1);
