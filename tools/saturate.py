#!/usr/bin/env python3
r"""saturate.py — the closing loop: one number for how linked the graph is.

`term_lint` and `undefined_lint` each surface bare terms, from different
angles and with different false positives, and both exit 0. That is right for
advisory checks and wrong for a loop: a loop needs a quantity that goes to
zero, and a way to move it. This driver computes that quantity and, with
`--fix`, moves the safe part of it.

Three counts, and only the third is the loop's:

  1. **registration** — every definition and equation card must have a row in
     `notation.md`. Nothing is auto-fixable here: naming a concept is a
     judgement, and a row written by a script would say nothing.
  2. **suppressed** — bare occurrences that are correctly bare. A later repeat
     in the same section (rules.md § 5 asks for the *first* occurrence), a
     card's own term inside its own Statement, a word swallowed by a longer
     phrase, anything inside maths or inside a link already.
  3. **missing** — a concept's first use in a Statement or a Proof, with no
     link on it. Counted two ways, because a concept enters a text two ways:
     by *name*, matched against the phrases a definition card claims, and by
     *symbol*, matched against `notation.md`'s symbol column. Only the first
     was ever counted, and mathematics is mostly written in the second — a
     statement can rest entirely on `\Theta_n` and never say the words. This
     is the number the loop drives to zero.

A fourth thing is printed and never counted: cards whose mathematics names no
other card. For a base definition that is correct. For a lemma it means the
argument cites nothing, which is either a proof standing on air or premises
left in prose — and a proof that consumes no stated premise is the one defect
the exact-match rule exists to prevent.

`--fix` inserts the links for the multi-word cases and re-runs `assign_ids`.
Single words are never auto-linked: `geodesic` occurs inside `closed
geodesic`, `geodesic ball`, `geodesic triangle` and `piecewise geodesic`, and
a substitution that cut one of those in half would link a reader to a card
that does not define what they clicked. Those are listed for a person.

Inserting a link into a Statement changes its id — deliberately, since a
Statement that now names its terms is a different text. So this is a batch one
runs on purpose, never a hook on save. Inserting one into a Proof changes no
id at all: only the Statement is hashed.

Usage: python3 tools/saturate.py [--fix]
"""
import re, sys, pathlib, subprocess
import sys as _sys; _sys.path.insert(0, str(__import__("pathlib").Path(__file__).parent)); import pools

V = pathlib.Path(__file__).resolve().parent.parent
FIX = '--fix' in sys.argv

# ---- the concept inventory --------------------------------------------------
concept_cards = [f for f in pools.atoms() if f.parent.name in ('definitions', 'equations')]
term2card = dict(pools.definition_terms())

# A definition's title names the notion the card is filed under. Its Statement
# usually defines several more, and marks each with emphasis the first time —
# `*spine*`, `*signature matrices*`, `*active rows*`. Those are the words a
# proof actually reaches for, and taking the inventory from titles alone left
# every one of them invisible: no tool could report `spine` as unlinked,
# because no tool knew `spine` was a defined term. Title claims still win a
# collision, and a term two cards both emphasise is dropped from both — an
# ambiguous term cannot be checked mechanically.
EMPH = re.compile(r'(?<!\*)\*([^*\n]{3,40})\*(?!\*)')
emph_claims = {}
for f in concept_cards:
    m = re.search(r'^## Statement\n(.*?)(?=\n## |\Z)', f.read_text(), re.S | re.M)
    if not m:
        continue
    for raw in EMPH.findall(m.group(1)):
        term = raw.strip().lower()
        if not term or ' of ' in term or any(c in term for c in '$[]'):
            continue
        for ph in (term, term + 's', term[:-1] if term.endswith('s') else term):
            if len(ph) < 4 or ph in term2card:
                continue
            emph_claims.setdefault(ph, set()).add(f.stem)
for ph, owners in emph_claims.items():
    if len(owners) == 1:
        term2card[ph] = next(iter(owners))
for f in concept_cards:                       # equation cards claim their title too
    if f.parent.name != 'equations':
        continue
    m = re.search(r'^#\s+.*?—\s*(.+)$', f.read_text(), re.M)
    if m:
        for ph in pools.phrases_of(m.group(1)):
            term2card.setdefault(ph, f.stem)
phrases = sorted(term2card, key=len, reverse=True)

# ---- registration -----------------------------------------------------------
notation = (pools.CLEAN[0] / 'notation.md').read_text()
registered = set(re.findall(r'\[\[([a-z0-9-]+)\]\]', notation))
ground_rows = re.findall(r'^\|\s*([^|]+?)\s*\|\s*[^|]+?\s*\|$', notation, re.M)
unregistered = sorted(f.stem for f in concept_cards if f.stem not in registered)

# ---- the symbol inventory ---------------------------------------------------
# Phrase matching finds a concept only when the text says its name. Mathematics
# mostly does not: a statement written in symbols mentions `\Theta_n` and never
# the words "unreduced angle vector", so a card can rest entirely on a notion it
# never links and every phrase-based check will call it closed. That was not a
# rare case here — it was every definition card and half the theorems.
#
# `notation.md` already carries the missing half of the map, symbol to defining
# card, and nothing read it for this. It does now.
#
# Never auto-fixable, and not because it is hard. A wikilink inside `$…$`
# renders as literal brackets (rules.md § 2), so the link cannot go on the
# symbol; it goes on a prose word beside it, and choosing that word is writing.
SYMBOL_ROW = re.compile(
    r'^\|\s*(.+?)\s*\|\s*[^|]*?\s*\|\s*\[\[([a-z0-9-]+)\]\]\s*\|$', re.M)
MATH = re.compile(r'\$\$(.*?)\$\$|\$([^$\n]*)\$', re.S)

sym2card = []
for shown, card in SYMBOL_ROW.findall(notation):
    for piece in re.findall(r'\$([^$]+)\$', shown):
        core = re.sub(r'\s+', '', piece)
        core = re.sub(r'\(.*?\)$', '', core)      # D_n(S) is used as D_n(anything)
        if len(core) >= 2:
            sym2card.append((core, card, shown.strip()))


def maths_of(body):
    """Every character of body that sits inside maths, whitespace removed."""
    return re.sub(r'\s+', '', ''.join(a or b for a, b in MATH.findall(body)))


def uses_symbol(maths, core):
    """Whether `core` occurs in `maths` as itself, not as a prefix of another.

    `N_n` sits inside `N_n^{\\mathrm{loopless}}`, and reporting the first
    because the text contains the second sends the reader to the wrong card —
    the general count instead of the restricted one. A registered symbol that
    strictly extends this one, occurring at the same place, wins.
    """
    longer = [c for c, _, _ in sym2card if c != core and c.startswith(core)]
    for m in re.finditer(re.escape(core), maths):
        if not any(maths.startswith(c, m.start()) for c in longer):
            return True
    return False


# ---- link saturation --------------------------------------------------------
def spans_to_skip(body):
    """Places a term may sit without owing a link.

    Inside an existing wikilink or embed; inside maths, where a wikilink would
    render as raw text; and on a callout header line, which is the statement's
    title rather than its prose (`assign_ids` drops those lines too).
    """
    out = [(m.start(), m.end()) for m in re.finditer(r'!?\[\[[^\]]*\]\]', body)]
    out += [(m.start(), m.end()) for m in re.finditer(r'\$\$.*?\$\$', body, re.S)]
    out += [(m.start(), m.end()) for m in re.finditer(r'\$[^$\n]*\$', body)]
    out += [(m.start(), m.end()) for m in re.finditer(r'^\s*>+\s*\[![a-z]+\].*$', body, re.M)]
    return out

SECTION = re.compile(r'^## (Statement|Proof)\n(.*?)(?=\n## |\Z)', re.S | re.M)


def sections_of(text):
    """(kind, body, offset) for the two sections that carry mathematics.

    Proofs are read as well as Statements. A proof names more concepts than the
    statement it proves — that is what a proof is — so leaving it out measured
    the smaller half and called the graph closed. It was left out because
    inserting a link *there* looked like the same edit; it is not. The id
    hashes the Statement alone, so a link added to a proof re-addresses
    nothing, which makes the proof the safer half to fix, not the riskier one.
    """
    for m in SECTION.finditer(text):
        yield m.group(1), m.group(2), m.start(2)


missing, suppressed, linked = [], 0, 0
edits = {}                                     # file -> list of (start, end, card, phrase)
silent = []                                    # cards naming no other card at all
symbol_missing, symbol_flagged = [], set()     # concept used as a symbol, never linked

for f in pools.atoms():
    text = f.read_text()
    secs = list(sections_of(text))
    if not secs:
        continue

    # "First occurrence" is per SECTION, not per card. Scoping it to the card
    # looks like a saving — the Statement already linked it, why say it twice —
    # and it silently exempts the whole Proof, which is the longer half and the
    # half a reader arrives at already scrolling. A 600-word proof carrying two
    # links inherited from the statement above it counted as closed. Statement
    # and Proof are read separately, so each owes its own first link.
    whole = ''.join(b for _, b, _ in secs)
    if not re.search(r'!?\[\[[a-z0-9-]+[\|\]]', whole):
        silent.append((f.stem, f.parent.name))

    for kind, body, base in secs:
        already_here = set(re.findall(r'!?\[\[([a-z0-9-]+)[\|\]]', body))
        linked += len(already_here)

        seen_math = maths_of(body)
        for core, card, shown in sym2card:
            if card == f.stem or card in already_here or not uses_symbol(seen_math, core):
                continue
            if (f.stem, card, kind) not in symbol_flagged:
                symbol_flagged.add((f.stem, card, kind))
                symbol_missing.append((f.stem, kind, shown, card))

        flagged = set()
        skip = spans_to_skip(body)
        low = body.lower()
        claimed = []
        for ph in phrases:                      # longest first
            card = term2card[ph]
            if card == f.stem:
                continue
            already = card in already_here
            first = True
            for occ in re.finditer(r'(?<![a-z])' + re.escape(ph) + r'(?![a-z])', low):
                s, e = occ.start(), occ.end()
                if any(a <= s < b for a, b in skip) or any(a <= s < e <= b for a, b in claimed):
                    claimed.append((s, e)); suppressed += 1; continue
                claimed.append((s, e))
                if already or not first or (f.stem, card, kind) in flagged:
                    suppressed += 1; continue
                first = False
                flagged.add((f.stem, card, kind))
                if ' ' in ph or '-' in ph:
                    edits.setdefault(f, []).append((base + s, base + e, card, body[s:e]))
                    missing.append((f.stem, ph, card, kind, True))
                else:
                    missing.append((f.stem, ph, card, kind, False))

auto = [x for x in missing if x[4]]
byhand = [x for x in missing if not x[4]]

print('concept coverage')
print(f'  definition + equation cards   {len(concept_cards):>4}')
print(f'  registered in notation.md     {len(concept_cards) - len(unregistered):>4}'
      f'  ({100 * (len(concept_cards) - len(unregistered)) // max(len(concept_cards),1)}%)')
print(f'  ground notions declared       {len(ground_rows):>4}')
for s in unregistered:
    # a paste-ready row, not an inserted one: naming a concept is the one part
    # of this loop a script must not do, and a row written by a machine would
    # say nothing a reader could not already read off the filename
    kind = 'Displayed formulas' if s.startswith('eq-') else 'the table'
    print(f'    UNREGISTERED  {s}')
    print(f'                  paste into {kind}:  | ? | ? | [[{s}]] |')
print()
print('link saturation (Statement and Proof sections)')
print(f'  concept uses already linked   {linked:>4}')
print(f'  correctly bare (suppressed)   {suppressed:>4}')
print(f'  first use missing a link      {len(missing):>4}'
      f'   ({len(auto)} auto-fixable, {len(byhand)} single-word, by hand)')
for stem, ph, card, kind, _ in auto:
    print(f'    FIX   {stem} ({kind}): "{ph}" -> [[{card}]]')
for stem, ph, card, kind, _ in byhand:
    print(f'    HAND  {stem} ({kind}): "{ph}" -> [[{card}]]  (single word — inside a compound?)')

# A card whose mathematics names no other card is either a genuine base — a
# definition everything else is built out of — or an argument that has quietly
# stopped citing its premises. The two are indistinguishable to a script and
# very distinguishable to a reader, so this is a list, not a gate. Definitions
# are separated out because for them silence is the normal case.
# The symbol half of the same question: not "did you name it" but "did you use
# it". A card can use `\Theta_n` throughout and link nothing, and until this ran
# nothing said so.
if symbol_missing:
    print()
    print('concept used as a symbol, with its defining card never linked')
    print(f'  uses{len(symbol_missing):>25}   (link a prose word beside the symbol, never the symbol)')
    for stem, kind, shown, card in symbol_missing:
        print(f'    SYMBOL  {stem} ({kind}): {shown} -> [[{card}]]')

if silent:
    base = [s for s, kind in silent if kind == 'definitions']
    rest = [s for s, kind in silent if kind != 'definitions']
    print()
    print('cards whose Statement and Proof name no other card')
    if rest:
        print(f'  statements  {len(rest):>4}   ← each one is a claim resting on nothing')
        for s in rest:
            print(f'    SILENT  {s}')
    if base:
        print(f'  definitions {len(base):>4}   (a base definition is expected to be silent)')
        for s in base:
            print(f'    base    {s}')

if FIX and edits:
    for f, es in edits.items():
        text = f.read_text()
        for start, end, card, shown in sorted(es, reverse=True):
            text = text[:start] + f'[[{card}|{shown}]]' + text[end:]
        f.write_text(text)
    print(f'\nrewrote {len(edits)} card(s); re-addressing')
    subprocess.run([sys.executable, str(V / 'tools' / 'assign_ids.py')], check=True)
    subprocess.run([sys.executable, str(V / 'tools' / 'gen_edges.py')], check=True)

print(f'\nsaturation: {len(missing)} phrase + {len(symbol_missing)} symbol '
      f'= {len(missing) + len(symbol_missing)} link(s) short of closed'
      + ('' if not unregistered else f', {len(unregistered)} card(s) unregistered'))
sys.exit(0)
