#!/usr/bin/env python3
"""Build local modules in dependency order with bounded memory and saved logs."""
import os, re, resource, signal, subprocess, sys, time
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
os.chdir(ROOT)
LIMIT_GIB = int(os.environ.get('LEAN_MEMORY_GIB', '32'))
LOGS = ROOT / '.lake' / 'verification_logs'
LOGS.mkdir(parents=True, exist_ok=True)
modules = {'.'.join(p.with_suffix('').parts): p for d in ('Dittert4', 'Dittert5', 'MerrisN4') for p in Path(d).rglob('*.lean')}
modules['MerrisN4'] = Path('MerrisN4.lean')
visited, order = set(), []
def visit(module):
    if module in visited: return
    visited.add(module)
    for dep in re.findall(r'^import\s+(\S+)', modules[module].read_text(), re.M):
        if dep in modules: visit(dep)
    order.append(module)
if sys.argv[1:2] == ['--single']:
    # Use only when imports are already built; Lake checks their freshness.
    order = sys.argv[2:]
else:
    for entry in (sys.argv[1:] or ['Dittert4.DH4DittertOneDiv52Fast', 'Dittert5.DH5Main', 'MerrisN4']):
        visit(entry)
def limits():
    resource.setrlimit(resource.RLIMIT_AS, (LIMIT_GIB * 1024**3, LIMIT_GIB * 1024**3))
    os.setsid()
def usage(pid):
    processes = {}
    for d in Path('/proc').iterdir():
        if not d.name.isdigit(): continue
        try:
            s = (d / 'status').read_text()
            parent = int(re.search(r'^PPid:\s+(\d+)', s, re.M)[1])
            rss = re.search(r'^VmRSS:\s+(\d+)', s, re.M)
            processes[int(d.name)] = (parent, int(rss[1]) if rss else 0)
        except (OSError, TypeError): pass
    children = {pid}
    while True:
        more = {p for p, (parent, _) in processes.items() if parent in children}
        if more <= children: break
        children |= more
    return sum(processes.get(p, (0, 0))[1] for p in children)
for i, module in enumerate(order, 1):
    log = LOGS / (module + '.log')
    start, peak = time.monotonic(), 0
    print(f'[{i}/{len(order)}] {module}', flush=True)
    with log.open('w') as out:
        p = subprocess.Popen(['lake', 'build', '+' + module], stdout=out, stderr=subprocess.STDOUT, preexec_fn=limits, env={**os.environ, 'LEAN_NUM_THREADS': '2'})
        while p.poll() is None:
            rss = usage(p.pid)
            peak = max(peak, rss)
            available = int(re.search(r'^MemAvailable:\s+(\d+)', Path('/proc/meminfo').read_text(), re.M)[1])
            if rss > 24 * 1024**2 or available < 8 * 1024**2:
                os.killpg(p.pid, signal.SIGTERM)
                p.wait()
                print(f'STOP memory protection: RSS={rss/1024**2:.2f} GiB available={available/1024**2:.2f} GiB', flush=True)
                sys.exit(2)
            time.sleep(2)
    print(f'  exit={p.returncode} elapsed={time.monotonic()-start:.1f}s peakRSS={peak/1024**2:.2f}GiB log={log}', flush=True)
    if p.returncode:
        print('\n'.join(log.read_text().splitlines()[-60:]), flush=True)
        sys.exit(p.returncode)
print('All requested modules built successfully.', flush=True)
