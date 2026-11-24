import { execFile } from 'node:child_process';
import { access } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { promisify } from 'node:util';

const execFileAsync = promisify(execFile);
const scriptDir = path.dirname(fileURLToPath(import.meta.url));
const rootDir = path.resolve(scriptDir, '..');
const leanDir = path.join(rootDir, 'formal', 'lean');

async function resolveLake() {
  const candidates = [process.env.LAKE_BIN, path.join(process.env.HOME ?? '', '.elan', 'bin', 'lake')].filter(Boolean);
  for (const candidate of candidates) {
    const resolved = path.resolve(candidate);
    try {
      await access(resolved);
      return resolved;
    } catch {
      // try next candidate
    }
  }
  return 'lake';
}

const lake = await resolveLake();
const { stdout, stderr } = await execFileAsync(lake, ['build'], {
  cwd: leanDir,
  maxBuffer: 10 * 1024 * 1024,
});
if (stdout) process.stdout.write(stdout);
if (stderr) process.stderr.write(stderr);
