#!/usr/bin/env python3
r"""Where the cards live — and everything else that is about THIS vault
rather than about the method. Every tool reads this file rather than naming a
directory, so instantiating the template is an edit here instead of an edit in
thirteen scripts; `tools/init.py` writes it for you.

The vault holds one curated pool per body of mathematics it is building, and
one raw pool of material cut mechanically from sources.

A card belongs to the pool it would still make sense in if the others
vanished. Boundary cases can be left where they land — the id is a hash of
the statement, so moving a card between pools changes neither its identity
nor any wikilink to it.

An edge belongs to the pool of its SOURCE: an edge is the source's assertion
that its statement or proof consumes the target, and the target may well live
in another pool.
"""
import pathlib

V = pathlib.Path(__file__).resolve().parent.parent

#: Curated pools, in the order tools should report them.
CLEAN = [V / 'HessenbergHypergraph']

#: Raw material, mechanically cut from sources. Never polished in place;
#: cards graduate OUT of it into a curated pool. Empty here: this vault has one
#: source, its own paper, and its cards are written by hand from the chapters
#: rather than cut mechanically and graduated. There is nothing to graduate
#: from, so `cardpool/` was removed rather than kept as an empty directory
#: implying a stage of the workflow that does not happen.
RAW = []

ALL = CLEAN + RAW

#: Vault layers that are not pools: prose that cites cards rather than being
#: one. Together with ALL and the chapters at the vault root, this is the
#: whole of what a tool reading "the vault" should read.
LAYERS = ['topics', 'notes', 'bibliography']

#: The card the network is grown from — `cone.py`'s default argument, and the
#: answer to "what is this vault for". Empty for a vault with no single root.
ROOT = 'thm-classification'

#: Where the Lean project lives, for the vault that has one — the directory
#: holding `lake-manifest.json` and `.lake/`. `V` when the vault root IS the
#: Lean project root; a subdirectory when the vault shares a repository with a
#: formalization that was there first. `lean_lint.py` reads only this.
LEAN = V / 'lean'

#: Surnames that must not appear in a Statement or Proof. Mathematics is
#: attributed in Notes and in the `references:` frontmatter, never in the
#: statement itself, and the names a given vault is tempted to write are the
#: ones its sources are by — so the list is per-vault. Regex fragments, so
#: `Tian(?![a-z])` is available when a surname is a prefix of a common word.
AUTHORS = ['Severini', r'Li(?![a-z])']


def atoms(pools=None):
    """Every atom file in the given pools (curated ones by default)."""
    for p in (pools if pools is not None else CLEAN):
        d = p / 'atoms'
        if d.exists():
            yield from sorted(d.rglob('*.md'))


def edges(pools=None):
    """Every edge file in the given pools (curated ones by default)."""
    for p in (pools if pools is not None else CLEAN):
        d = p / 'edges'
        if d.exists():
            yield from sorted(d.rglob('*.md'))


def files(pools=None):
    """Every markdown file in the given pools."""
    for p in (pools if pools is not None else CLEAN):
        if p.exists():
            yield from sorted(p.rglob('*.md'))


def vault_md():
    """Every markdown file that is vault content — pools, layers, chapters.

    Some tools read the whole vault rather than the pools, because a rendering
    defect in a chapter is as visible as one in a card. Reaching that by
    globbing the vault root was fine while a vault was only ever a vault; it
    stops being fine as soon as one shares its repository with a Lean library
    or a generated site, which bring their own markdown — Lake's package store,
    a documentation generator's licence page. Naming those to skip them is a
    list that grows with every new neighbour. What the vault contains is short,
    known, and already declared above, so declare it instead.
    """
    seen = set()
    for d in ALL + [V / n for n in LAYERS]:
        if d.exists():
            seen.update(d.rglob('*.md'))
    seen.update(V.glob('*.md'))          # the chapters, README, FRONTIER
    return sorted(seen)


def pool_of(path):
    """Which pool a file sits in, or None."""
    path = pathlib.Path(path).resolve()
    for p in ALL:
        if str(path).startswith(str(p.resolve()) + '/'):
            return p
    return None


#: Words a definition's title may end on that name nothing — dropped before a
#: phrase is offered as a term. Without this the checker claims the word "the".
_STOP = {'a', 'an', 'the', 'of', 'and', 'or', 'its', 'for', 'under', 'with', 'to', 'in'}


def phrases_of(title):
    """Every term a definition card claims, from the text after its em-dash.

    A title naming several notions is split on commas and `and`, and each part
    is offered in singular and plural.

    Deliberately NOT reduced to a head noun. "The dimensions of a convex set"
    would give "dimensions", which then fires inside "Hausdorff dimension",
    "three dimensions" and every other ordinary use of the word — English is
    ambiguous there and no rule recovers it. A checker that reports seventy
    guesses is worse than one that reports five facts.
    """
    import re
    core = title.split('\u2014')[-1].strip().lower()
    core = re.sub(r'\(.*?\)', '', core)
    out = set()
    for part in re.split(r',| and ', core):
        part = part.strip().strip('.')
        part = re.sub(r'^(?:a|an|the) ', '', part)
        if not part or part in _STOP or len(part) < 4:
            continue
        out.add(part)
        out.add(part[:-1] if part.endswith('s') else part + 's')
    return out


def definition_terms(pools=None):
    """term -> the definition card that claims it.

    A phrase two cards both claim is dropped from both. An ambiguous term
    cannot be checked mechanically — reporting it against either card would
    be a guess — and head-noun extraction manufactures such collisions, so
    the rule pays for itself.
    """
    import re, collections
    claims = collections.defaultdict(set)
    for f in atoms(pools):
        if f.parent.name != 'definitions':
            continue
        h = re.search(r'^#\s+.*?\u2014\s*(.+)$', f.read_text(), re.M)
        if not h:
            continue
        for ph in phrases_of(h.group(1)):
            claims[ph].add(f.stem)
    return {ph: next(iter(s)) for ph, s in claims.items() if len(s) == 1}
