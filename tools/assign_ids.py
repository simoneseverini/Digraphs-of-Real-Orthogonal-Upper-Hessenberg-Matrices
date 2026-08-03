#!/usr/bin/env python3
r"""assign_ids.py — content-addressed ids for the hypergraph.

Every atom card gets frontmatter `id:` = sha256 of its normalized
Statement (the callout body under `## Statement`, '>' prefixes stripped,
whitespace collapsed), truncated to 12 hex chars. Every edge gets
`id:` = sha256 of "kind:source_id:target_id" — so an edge's address
changes exactly when its semantics or either endpoint's content changes.

Filenames stay the readable slugs (wikilinks untouched); the id is the
stable mathematical address. Idempotent: rerun after edits to refresh.

Usage: python3 tools/assign_ids.py
"""
import hashlib, pathlib, re
import sys as _sys; _sys.path.insert(0, str(__import__("pathlib").Path(__file__).parent)); import pools

V = pathlib.Path(__file__).resolve().parent.parent
POOLS = pools.ALL
def _glob(sub):
    for p in POOLS:
        d = p / sub
        if d.exists():
            yield from sorted(d.rglob('*.md'))

def sha(s):
    return hashlib.sha256(s.encode()).hexdigest()[:12]

def set_id(text, hid):
    if re.search(r'^id: ', text, re.M):
        return re.sub(r'^id: .*$', f'id: {hid}', text, count=1, flags=re.M)
    return text.replace('---\n', f'---\nid: {hid}\n', 1)

def _equation_bodies():
    """stem -> normalized Statement, for every equation card.

    A card may display an equation card inside its own Statement, with an
    `![[embed]]`, so that one formula is written once and renders wherever it
    is used. That is a presentation win and an addressing hazard: the id
    hashes the Statement, and a Statement reading `![[eq-foo]]` hashes the
    *name* rather than the mathematics — edit `eq-foo` and every card that
    displays it would silently say something else at an unchanged address.
    So the embed is spliced in before hashing. An equation's content is part
    of the content of everyone who shows it, and their ids move with it.
    """
    out = {}
    for f in _glob('atoms'):
        if f.parent.name == 'equations':
            out[f.stem] = _body(f.read_text(), {})
    return out

def _body(text, equations):
    m = re.search(r'^## Statement\s*$', text, re.M)
    seg = text[m.end():] if m else re.sub(r'^---.*?---', '', text, count=1, flags=re.S)
    lines = []
    started = False
    for ln in seg.split('\n'):
        if ln.lstrip().startswith('>'):
            started = True
            s = re.sub(r'^\s*>+\s?', '', ln)
            if re.match(r'\[![a-z]+\]', s):        # callout header carries no math
                continue
            lines.append(s)
        elif started and ln.strip():
            break
    body = ' '.join(lines) if lines else re.sub(r'^---.*?---', '', text, count=1, flags=re.S)
    # the display half of [[stem|hash]] is presentation, not content — fold it
    # away so refreshing displayed hashes can never change an id (no cascades)
    body = re.sub(r'\[\[([^\]|]+)\|[^\]]+\]\]', r'[[\1]]', body)
    body = re.sub(r'!\[\[([^\]|#]+)(?:\|[^\]]*)?\]\]',
                  lambda m: equations.get(m.group(1).strip(), m.group(0)), body)
    return re.sub(r'\s+', ' ', body).strip()

def statement_body(text, equations=None):
    return _body(text, equations if equations is not None else {})

def main():
    ids = {}                                        # stem -> id
    changed = 0
    equations = _equation_bodies()
    for f in _glob('atoms'):
        t = f.read_text()
        hid = sha(statement_body(t, equations))
        ids[f.stem] = hid
        t2 = set_id(t, hid)
        if t2 != t:
            f.write_text(t2); changed += 1
    e_changed = skipped = 0
    for f in _glob('edges'):
        t = f.read_text()
        kind = (re.search(r'^kind: (\S+)', t, re.M) or [None, '?'])[1]
        refs = re.findall(r'"\[\[([^\]]+)\]\]"', t)
        if len(refs) != 2 or refs[0] not in ids or refs[1] not in ids:
            skipped += 1
            continue
        hid = sha(f"{kind}:{ids[refs[0]]}:{ids[refs[1]]}")
        t2 = set_id(t, hid)
        if t2 != t:
            f.write_text(t2); e_changed += 1
    print(f"cards: {len(ids)} ({changed} written)  edges updated: {e_changed}  edges skipped: {skipped}")
    dup = len(ids) - len(set(ids.values()))
    print(f"id collisions: {dup}")

if __name__ == '__main__':
    main()
