#!/usr/bin/env python3
r"""boundary_lint.py — every named result a proof leans on must be somewhere.

`frontier.py` asks whether a card has a Proof section. It does not ask whether
that proof's citations resolve, and nothing else did either — so a card could
be marked `proved` while its argument turned on a theorem the network never
states. Ten of them did: Nash's embedding, Smale's theorem, Alexandrov
comparison, the Thom isomorphism, Arzelà–Ascoli, and the rest were consumed
inside proofs and declared nowhere.

`rules.md` § 4 already says what should happen: every notion is a card, a
fact card, or a declared ground notion, and anything else is an undeclared
debt. This is the check for that clause, restricted to the case a machine can
recognise — a *named* result, which is the case that matters, because an
argument leaning on someone's theorem is exactly where a network stops being
self-contained.

What counts as named: a capitalised surname (or a hyphenated pair) followed by
a possessive and one of theorem, inequality, lemma, isomorphism, embedding,
conjecture, criterion, comparison — or the same words preceded by the name.
The list of unnamed-but-external notions at the bottom is maintained by hand,
because no pattern recognises "partition of unity" as an import.

Resolution means: a card whose title contains the name, or a row in
`notation.md` (either table, or the ground notions). Exit 1 on any hit.

Usage: python3 tools/boundary_lint.py
"""
import re, sys, pathlib
import sys as _sys; _sys.path.insert(0, str(__import__("pathlib").Path(__file__).parent)); import pools

V = pathlib.Path(__file__).resolve().parent.parent

NAMED = re.compile(
    r"\b([A-Z][a-zé]+(?:[-–][A-Z][a-zé]+)?)(?:'s)?\s+"
    r"(theorem|inequality|lemma|isomorphism|embedding|conjecture|criterion|comparison|constant)\b")

# Imports no pattern will recognise, because they are named after what they are
# rather than after anybody. Add to this list when a proof starts leaning on a
# new one; that is the point of the list being here rather than inferred.
UNNAMED = ['partition of unity', 'relative homology', 'cap product', 'winding number',
           'normal bundle', 'tubular neighbourhood', 'deformation retract',
           'isoperimetric', 'degree one', 'law of cosines']

notation = (pools.CLEAN[0] / 'notation.md').read_text().lower()
titles = {}
for f in pools.atoms():
    m = re.search(r'^#\s+(.*)$', f.read_text(), re.M)
    titles[f.stem] = (m.group(1) if m else '').lower()
haystack = ' '.join(titles.values()) + ' ' + ' '.join(titles.keys()).replace('-', ' ') + ' ' + notation
# `Morrey's inequality` in a title and `Morrey inequality` in a proof are the
# same import; the possessive is grammar, not identity.
haystack = haystack.replace("'s ", ' ').replace('\u2019s ', ' ').replace('\u2013', '-')

def resolves(*parts):
    """A name resolves only together with what kind of thing it names.

    Matching the surname alone was not enough: `def-thom-class` made "Thom
    isomorphism" resolve, and the isomorphism is a different statement from
    the class — the one the network defines, the other the one it imports.
    """
    for sep in (' ', '-'):
        probe = sep.join(parts).lower().replace('\u2013', '-').replace("'s ", ' ')
        if probe in haystack or probe.replace('-', ' ') in haystack:
            return True
    return False

bad = []
for f in pools.atoms():
    t = f.read_text()
    for sec in ('Statement', 'Proof'):
        m = re.search(rf'## {sec}\n(.*?)(?=\n## |\Z)', t, re.S)
        if not m:
            continue
        body = m.group(1)
        seen = set()
        own = titles[f.stem]
        for name, kind in NAMED.findall(body):
            if name.lower() in own:      # a card may name itself
                continue
            if name in ('The', 'This', 'A', 'An', 'Let', 'By', 'Then', 'Since', 'For', 'It', 'Both', 'Its'):
                continue
            if (name, kind) in seen or resolves(name, kind):
                continue
            seen.add((name, kind))
            bad.append((f, f'{sec} leans on "{name} {kind}", which is neither a card nor declared'))
        for u in UNNAMED:
            if u in body.lower() and not resolves(u):
                bad.append((f, f'{sec} leans on "{u}", which is neither a card nor declared'))

if bad:
    for f, msg in sorted(bad, key=lambda x: str(x[0]))[:40]:
        print(f'{f.relative_to(V)}: {msg}')
    print(f'\n{len(bad)} undeclared import(s).')
    sys.exit(1)
print('boundary lint: clean')
