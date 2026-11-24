import { spawn } from 'node:child_process';
import { access } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const scriptDir = path.dirname(fileURLToPath(import.meta.url));
const rootDir = path.resolve(scriptDir, '..');
const tlaDir = path.join(rootDir, 'formal', 'tla');

const SPECS = ['L1Coherence', 'FetchSingleFlight'];

async function resolveJar() {
  const candidates = [
    process.env.TLA2TOOLS_JAR,
    '/Volumes/Scratch/lru-cache-clustered/tmp/tla2tools.jar',
    path.join(process.env.HOME ?? '', '.tla', 'tla2tools.jar'),
  ].filter(Boolean);

  for (const candidate of candidates) {
    try {
      await access(candidate);
      return candidate;
    } catch {
      // try next candidate
    }
  }

  throw new Error(
    `tla2tools.jar not found. Set TLA2TOOLS_JAR=/path/to/tla2tools.jar (checked: ${candidates.join(', ')}).`,
  );
}

function runTlc(jar, metaDir, spec) {
  const tlaFile = path.join(tlaDir, `${spec}.tla`);
  const cfgFile = path.join(tlaDir, `${spec}.cfg`);
  console.log(`\n==> TLC model-checking ${spec}`);
  return new Promise((resolve, reject) => {
    const child = spawn(
      'java',
      [
        '-XX:+UseParallelGC',
        '-cp',
        jar,
        'tlc2.TLC',
        '-workers',
        'auto',
        '-deadlock',
        '-cleanup',
        '-metadir',
        path.join(metaDir, spec),
        '-config',
        cfgFile,
        tlaFile,
      ],
      { cwd: tlaDir, stdio: 'inherit' },
    );
    child.on('error', reject);
    child.on('exit', (code) => {
      if (code === 0) resolve();
      else reject(new Error(`TLC failed for ${spec} with exit code ${String(code)}`));
    });
  });
}

const jar = await resolveJar();
const metaDir = process.env.TLC_METADIR ?? '/Volumes/Scratch/lru-cache-clustered/tmp/tlc-states';

for (const spec of SPECS) {
  await runTlc(jar, metaDir, spec);
}
