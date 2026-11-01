// env.js: load settings such as ANTHROPIC_API_KEY from a `.env` file in the
// project root, if there is one. `.env` is git-ignored, so the key never goes
// into the repository. Imported first by server.js, before anything reads the
// environment. Variables already set in the shell win over the file.
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const file = path.join(path.dirname(fileURLToPath(import.meta.url)), "..", ".env");
if (fs.existsSync(file)) process.loadEnvFile(file);
