#!/usr/bin/env python3
r"""structure_lint.py — the failures no other check can see.

Three defects, each of which passed every existing linter while being wrong.

  1. **A second `## Statement`.** `assign_ids` takes the first one and runs to
     the next `## Notes`, so a card with two Statement sections hashes both,
     or hashes the first plus whatever sits between them. It renders fine, it
     lints clean, and its address means nothing. This happened twice while
     these cards were being written, both times because a card wanted to say
     two things and a second section looked like the way to do it.
  2. **A `references:` entry that resolves to nothing.** Frontmatter is read by
     no other tool — `gen_edges` and `edge_lint` scan Statement and Proof only
     — so a mistyped `[[ref-...]]` there is invisible until a reader clicks it.
  3. **Terminology drift.** `notation.md` carries a table of the form "this
     network says X, not Y". That table is prose until something checks it:
     the whole point of choosing one word is that the other stops appearing.

Exit 1 on any hit. Usage: python3 tools/structure_lint.py
"""
import re, sys, pathlib
import sys as _sys; _sys.path.insert(0, str(__import__("pathlib").Path(__file__).parent)); import pools

V = pathlib.Path(__file__).resolve().parent.parent
KNOWN = {'Statement', 'Proof', 'Notes', 'References'}
bad = []

refs = {p.stem for p in (V / 'bibliography' / 'references').glob('ref-*.md')}
stems = {f.stem for f in pools.atoms()}

for f in pools.atoms():
    t = f.read_text()
    heads = re.findall(r'^## (.+)$', t, re.M)
    for h in heads:
        if h.strip() not in KNOWN:
            bad.append((f, f'unknown section "## {h.strip()}" — the id is hashed from '
                           f'`## Statement` to the next known heading'))
    if heads.count('Statement') != 1:
        bad.append((f, f'{heads.count("Statement")} `## Statement` sections, expected exactly 1'))
    if heads != sorted(heads, key=lambda h: ['Statement', 'Proof', 'Notes', 'References'].index(h)
                       if h in KNOWN else 99):
        bad.append((f, f'sections out of order: {" · ".join(heads)}'))

    fm = re.match(r'\A---\n(.*?)\n---\n', t, re.S)
    for target in re.findall(r'\[\[([a-z0-9-]+)', fm.group(1) if fm else ''):
        if target not in refs and target not in stems:
            bad.append((f, f'frontmatter cites [[{target}]], which is neither a reference card nor an atom'))

# ---- the terminology table, made executable ---------------------------------
notation = (pools.CLEAN[0] / 'notation.md').read_text()
sec = re.search(r'## Terminology\n(.*?)(?=\n## )', notation, re.S)
retired = []
for row in re.findall(r'^\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|$', sec.group(1) if sec else '', re.M):
    keep, drop, _why = row
    if keep in ('This network', '---') or drop in ('Not', '---'):
        continue
    retired.append((keep.strip(), drop.strip()))

for f in pools.atoms():
    t = f.read_text()
    m = re.search(r'## Statement\n(.*?)(?=\n## |\Z)', t, re.S)
    if not m:
        continue
    body = m.group(1)
    if re.search(r'^verbatim:', t, re.M):
        continue                      # a source's own words are not ours to police
    for keep, drop in retired:
        if re.search(r'(?<![a-z])' + re.escape(drop) + r'(?![a-z])', body, re.I):
            bad.append((f, f'Statement says "{drop}"; this network says "{keep}" (notation.md § Terminology)'))

if bad:
    for f, msg in bad[:40]:
        print(f'{f.relative_to(V) if hasattr(f, "relative_to") else f}: {msg}')
    print(f'\n{len(bad)} offender(s).')
    sys.exit(1)
print('structure lint: clean')
