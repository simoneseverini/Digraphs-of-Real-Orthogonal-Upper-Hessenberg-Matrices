#!/usr/bin/env python3
r"""gen_lean.py — derive each card's `lean:` block from what already records it.

A card's formal counterpart is not something to type twice. This repository
states the pairing in two places already, and both are checked by something:

  * `site/blueprint/src/content.tex` — `\lean{…}` bindings, fully qualified.
    leanblueprint hands these to the elaborator, so a name that does not
    resolve fails the build. This is the authority and wins every collision.
  * `paper/sections/*.tex` — `\leanmargin{decl}{path}` in the compiled section,
    `\leanlink{file}{lines}{decl}` in the two that are not compiled. The first
    carries a file path and so can be qualified; the second carries the short
    names of the single-file era, before the library was split into
    `Combinatorial/`, `Matrix/` and `Realization/`, and is resolved here by
    matching the last component against the built library.

What this writes is only `- decl:` lines. `lean_lint.py --fix` fills in
`module`, `line`, `state` and `rev` by finding the declaration in the
checkout — the same division of labour as everywhere else here: a human (or a
source) names the thing, a tool resolves where it currently lives, and a line
number is never written by hand because Mathlib moves and a hand-written one
goes quietly false.

Usage: python3 tools/gen_lean.py [--write]
       --write   insert the blocks into the cards (then run lean_lint.py --fix)
"""
import pathlib, re, sys

sys.path.insert(0, str(pathlib.Path(__file__).parent)); import pools

V = pathlib.Path(__file__).resolve().parent.parent
WRITE = '--write' in sys.argv

#: Which card each of the sources' labels became. The one thing that cannot be
#: derived: a card is named for what it says, a label for where it sat.
LABEL2CARD = {
    'def:OH': 'def-orthogonal-upper-hessenberg',
    'def:supp': 'def-support-digraph',
    'def:support': 'def-support-digraph',
    'def:sign': 'def-sign-equivalence',
    'cor:sign-support': 'cor-sign-invariance-of-support-digraph',
    'def:givens': 'def-givens-rotation',
    'def:active': 'def-active-set',
    'def:active-set': 'def-active-set',
    'ex:D6S24': 'ex-d6-s24',
    'ex:D5S2': 'ex-d5-s2',
    'ex:D5S13': 'ex-d5-s13',
    'thm:univ': 'thm-universality',
    'thm:universality': 'thm-universality',
    'thm:bridge': 'thm-bridge',
    'thm:rigid': 'thm-rigidity',
    'thm:class': 'thm-classification',
    'thm:classification': 'thm-classification',
    'thm:count': 'thm-enumeration',
    'thm:count-loopless': 'thm-loopless-enumeration',
    'thm:count_loopless': 'thm-loopless-enumeration',
    'thm:loopless-nonisomorphic': 'thm-loopless-enumeration',
    'lem:unique-hc': 'lem-unique-hamilton-cycle',
    'prop:degrees': 'prop-degree-formulas',
    'lem:one': 'lem-singleton-isomorphism',
    'lem:loops-in-model': 'lem-loops-in-model',
    'cor:loopless-characterization': 'cor-loopless-characterization',
}

#: A card whose statement the sources never paired with a declaration. Listed
#: rather than left silent: the cut lemma IS formalized — it is the `cut_lemma`
#: the unique-Hamilton-cycle lemma names — but the paper attributes it to that
#: lemma's environment, and splitting one environment's bindings across two
#: cards is a judgement no extractor should make.
EXTRA = {
    'lem-cut': ['cut_lemma'],
    'def-unreduced-angle-vector': ['UnreducedAngles'],
}

#: Renamed since the two uncompiled sections were written. Those carry the
#: names of the single-file era; the library was later split into folders and
#: the declarations were renamed with it — `_one`/`_n` became `_first`/`_last`,
#: and the membership lemma spelled out what R and C are. Recorded here rather
#: than corrected in `paper/`: those sections are not compiled and editing them
#: would be editing the paper to suit a tool.
RENAMED = {
    'loop_iff_mem_R_and_C': 'loop_iff_mem_activeRows_and_activeCols',
    'loop_at_one': 'loop_at_first',
    'loop_at_n': 'loop_at_last',
    'outDeg_one': 'outDeg_first',
    'inDeg_n': 'inDeg_last',
}


def index_library():
    """last component -> fully-qualified names defined in THIS library."""
    out = {}
    ns = re.compile(r'^namespace\s+(\S+)')
    end = re.compile(r'^end\s+(\S+)\s*$')
    # `private` is skipped: a card names its formal counterpart so a reader can
    # go and look at it, and a private declaration is not part of the library's
    # public surface. The universality theorem has one of each name — the
    # private workhorse and the public statement — and the card wants the
    # second.
    decl = re.compile(
        r'^(?:@\[[^\]]*\]\s*)?(?:protected\s+|noncomputable\s+|partial\s+'
        r'|unsafe\s+|nonrec\s+)*(?:theorem|lemma|def|abbrev|instance|structure|inductive)\s+'
        r'([^\s({\[:]+)')
    for f in (pools.LEAN).rglob('*.lean'):
        if '/.lake/' in str(f):
            continue
        stack = []
        for ln in f.read_text(errors='replace').split('\n'):
            if (m := ns.match(ln)):
                stack.append(m.group(1)); continue
            if (m := end.match(ln)):
                if stack and stack[-1] == m.group(1):
                    stack.pop()
                continue
            if (m := decl.match(ln)):
                full = '.'.join(stack + [m.group(1)])
                out.setdefault(m.group(1).split('.')[-1], []).append(full)
    return out


def from_blueprint():
    p = V / 'site' / 'blueprint' / 'src' / 'content.tex'
    if not p.exists():
        return {}
    out = {}
    for m in re.finditer(r'\\begin\{(theorem|lemma|proposition|corollary|definition)\}'
                         r'(.*?)\\end\{\1\}', p.read_text(), re.S):
        lab = re.search(r'\\label\{([^}]*)\}', m.group(2))
        if not lab:
            continue
        decls = []
        for d in re.findall(r'\\lean\{([^}]*)\}', m.group(2)):
            decls += [x.strip() for x in d.split(',') if x.strip()]
        if decls:
            out[lab.group(1)] = decls
    return out


def from_paper():
    out = {}
    S = V / 'paper' / 'sections'
    t = (S / 'sec-results.tex').read_text()
    for m in re.finditer(r'\\label\{([^}]*)\}\s*\n\\leanmargin(two)?\{([^}]*)\}\{[^}]*\}'
                         r'(?:\{([^}]*)\}\{[^}]*\})?', t):
        lab, _, d1, d2 = m.groups()
        out.setdefault(lab, []).extend(d.replace('\\', '') for d in (d1, d2) if d)
    for name in ('sec-enumeration.tex', 'sec-loopless.tex'):
        t = (S / name).read_text()
        for env in re.finditer(r'\\begin\{(?:lemma|proposition|theorem|corollary)\}'
                               r'\[(.*?)\]\\label\{([^}]*)\}', t, re.S):
            decls = [d.replace('\\', '') for d in
                     re.findall(r'\\leanlink\{[^}]*\}\{[^}]*\}\{([^}]*)\}', env.group(1))]
            if decls:
                out.setdefault(env.group(2), []).extend(decls)
    return out


def main():
    index = index_library()
    blueprint, paper = from_blueprint(), from_paper()

    per_card = {}
    for src, name in ((paper, 'paper'), (blueprint, 'blueprint')):   # blueprint last: it wins
        for lab, decls in src.items():
            card = LABEL2CARD.get(lab)
            if not card:
                print(f'  UNMAPPED  {lab} ({name}) — add it to LABEL2CARD')
                continue
            per_card.setdefault(card, {'decls': [], 'via': set()})
            per_card[card]['via'].add(name)
            for d in decls:
                if d not in per_card[card]['decls']:
                    per_card[card]['decls'].append(d)
    for card, decls in EXTRA.items():
        per_card.setdefault(card, {'decls': [], 'via': set()})['via'].add('by hand')
        per_card[card]['decls'] += [d for d in decls if d not in per_card[card]['decls']]

    # qualify every short name against the built library
    cards = {f.stem: f for f in pools.atoms()}
    written, unresolved = 0, []
    for card, info in sorted(per_card.items()):
        if card not in cards:
            print(f'  NO SUCH CARD  {card}')
            continue
        qualified = []
        for d in (RENAMED.get(x, x) for x in info['decls']):
            if '.' in d and d.split('.')[0][0].isupper() and d in sum(index.values(), []):
                qualified.append(d); continue
            hits = index.get(d.split('.')[-1], [])
            exact = [h for h in hits if h == d or h.endswith('.' + d)]
            pick = (exact or hits)
            if len(pick) == 1:
                qualified.append(pick[0])
            elif pick:
                qualified.append(pick[0])
                print(f'  AMBIGUOUS {card}: {d} -> {len(pick)} hits, took {pick[0]}')
            else:
                unresolved.append((card, d))
        # The blueprint is the authority, so when it has already named a
        # declaration in full, a short name from the paper that resolves to the
        # same last component is that same statement said less precisely — not a
        # second one. Keep the qualified one.
        from_bp = {d for d in info['decls'] if '.' in d and d in qualified}
        tails = {d.rsplit('.', 1)[-1] for d in from_bp}
        qualified = [d for d in qualified
                     if d in from_bp or d.rsplit('.', 1)[-1] not in tails]
        # Two sources naming the same declaration — the blueprint in full, the
        # paper by its short name — resolve to one fully-qualified string, and
        # the card wants it once.
        qualified = list(dict.fromkeys(qualified))
        if not qualified:
            continue
        print(f'  {card:40} {len(qualified):2} decl(s)  via {"+".join(sorted(info["via"]))}')
        if WRITE:
            f = cards[card]
            t = f.read_text()
            if re.search(r'^lean:', t, re.M):
                t = re.sub(r'^lean:\n(?:  - .*\n(?:    .*\n)*)+', '', t, flags=re.M)
            block = 'lean:\n' + ''.join(f'  - decl: {d}\n' for d in qualified)
            t = re.sub(r'^(type: .*\n)', r'\1' + block, t, count=1, flags=re.M)
            f.write_text(t)
            written += 1

    for card, d in unresolved:
        print(f'  UNRESOLVED  {card}: {d} is in no .lean file under {pools.LEAN.name}/')
    print(f'\n{len(per_card)} card(s) paired, {len(unresolved)} declaration(s) unresolved'
          + (f', {written} card(s) written' if WRITE else ''))
    if not WRITE:
        print('re-run with --write, then python3 tools/lean_lint.py --fix')
    return 1 if unresolved else 0


if __name__ == '__main__':
    sys.exit(main())
