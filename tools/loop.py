#!/usr/bin/env python3
r"""loop.py — one turn of the cycle, in the one order that is correct.

The steps are not interchangeable and the dependencies are not obvious:

  * `gen_bib` rebuilds `bibliography/references.bib` from the reference cards,
    which are its source of truth — `bib_lint` fails if the two have drifted,
    and running it by hand was the only thing keeping them together;
  * `gen_edges` rebuilds `edges/` from the links in the cards, so it must run
    after the cards are edited and before anything reads the graph;
  * `assign_ids` addresses the cards *and then* the edges, whose ids are
    `sha256(kind : source-id : target-id)` — so it must run after `gen_edges`,
    or it addresses edges that no longer exist;
  * `saturate` may rewrite Statements, which changes ids, so with `--fix` it
    re-runs `assign_ids` itself and must come before the checks, not after;
  * the linters are pure readers and may run in any order, but their exit
    codes are the gate;
  * `frontier` writes `FRONTIER.md` and recomputes every `status:`, which is
    an edit, so it goes last.

Running them by hand in the wrong order does not fail loudly. It leaves the
edge ids stale, which is a defect no check reports because every file is
individually well-formed.

Usage:
    python3 tools/loop.py            # wire, address, check, report
    python3 tools/loop.py --fix      # also insert the safe missing links
"""
import subprocess, sys, pathlib

V = pathlib.Path(__file__).resolve().parent.parent
T = V / 'tools'
PY = sys.executable
FIX = '--fix' in sys.argv

GATES = ['structure_lint', 'boundary_lint', 'render_lint', 'noise_lint', 'edge_lint', 'bib_lint',
         'figure_lint', 'hedge_lint']
ADVISORY = ['notation_lint', 'bundle_lint', 'shared_lint', 'rigor_lint']

def run(script, *args, capture=True):
    r = subprocess.run([PY, str(T / f'{script}.py'), *args],
                       capture_output=capture, text=True)
    return r

def tail(r, n=1):
    out = (r.stdout or '') + (r.stderr or '')
    lines = [l for l in out.strip().split('\n') if l.strip()]
    return ' / '.join(lines[-n:]) if lines else ''

print('── wiring ' + '─' * 50)
for step in ('gen_bib', 'gen_edges', 'assign_ids'):
    print(f'  {step:<14} {tail(run(step))}')

print('── saturation ' + '─' * 46)
r = run('saturate', *(['--fix'] if FIX else []))
sat = r.stdout or ''
for line in sat.strip().split('\n'):
    if line.startswith(('  ', 'saturation')) and 'FIX' not in line and 'HAND' not in line:
        print('  ' + line.strip())
for line in sat.split('\n'):
    if 'FIX ' in line or 'HAND ' in line or 'UNREGISTERED' in line:
        print('  ' + line.strip())
if FIX:
    run('gen_edges'); run('assign_ids')

print('── gates ' + '─' * 51)
failed = []
for lint in GATES:
    r = run(lint)
    ok = r.returncode == 0
    if not ok:
        failed.append(lint)
    print(f'  {"ok " if ok else "FAIL"} {lint:<16} {tail(r, 3 if not ok else 1)}')

print('── advisory ' + '─' * 48)
for lint in ADVISORY:
    print(f'      {lint:<16} {tail(run(lint))}')

print('── state ' + '─' * 51)
r = run('frontier')
print('  ' + tail(r, 6).replace(' / ', '\n  '))

print()
if failed:
    print(f'BLOCKED: {", ".join(failed)}')
    sys.exit(1)
print('loop: clean')
