---
type: rules
---

# The rules of this graph

What a node is, what an edge means, and what may appear where. The
mechanical half — text and graph mirroring each other, no undeclared notion,
uniform notation — is enforced by `tools/*_lint.py` rather than left to
habit. None of it is verification: a card can pass every check and still be
false, and the rule that carries the weight — exact match — is judged by a
person. What the checks buy is structural rigidity, which is what makes a
network worth formalizing from.

## 1 · Nodes (atoms)

One card per mathematical statement, filed under `atoms/<type>s/`:
`theorem`, `proposition`, `lemma`, `corollary`, `claim`, `conjecture`,
`example`, `equation`, `remark`, `definition`.

`equation` is for a displayed relation that the text refers to by name and that
asserts nothing on its own — a functional's formula, a normalisation identity,
a coordinate expression. A numbered display that *claims* something is not an
equation card: it is a lemma, and it owes a proof. This distinction is what a
source's equation numbering hides, since `(2.1)` is a position in a document
and says nothing about what kind of object sits there.

An equation card **may be displayed inside another card's Statement**, with an
`![[embed]]`, so that a formula is written once and renders wherever it is
used. Two consequences, both handled by the tools rather than by discipline:
the embed counts as a `references` edge, since the source's text invokes the
target; and `assign_ids.py` splices the equation's Statement in before
hashing, so an id still addresses mathematics and not a filename. Editing an
equation therefore moves the id of every card that shows it, which is the
correct behaviour — their statements did change.

`conjecture` is for a statement somebody *posed as a question* — a problem the
network names but does not turn on. The card records the question, not its
fate: whether it has since been settled, and by what, belongs in its Notes. A
settled conjecture stays a conjecture card, because what it contributes to the
network is the question it asked. It is not a `claim` (which is something this
network asserts and owes a proof for) and not a `debt` (a proof this network
still owes); see § 3.

```
---
id: 7a4b8dc3d01c    sha256 of the normalized Statement — the identity
type: theorem
references:         (optional; provenance is metadata, not content.
  - "[[ref-x|Author, §n]]"   one quoted wikilink per citation — the locus
  - "[[pool-card]]"          in the display text; pool cards bare; a
  - "plain citation"         source without a bibliography card stays a
---                          plain string. Never hashed.)
# Theorem — <content-descriptive title>
<optional intro>      one or two sentences of intuition — what the object
                    looks like and why it exists; provenance belongs in
                    the references frontmatter. Never hashed.
## Statement
## Proof            (folded; absent = status: debt, see § Status)
## Notes            (folded callout like Proof; free commentary, never
                    hashed — background, intuition, figures:
                    ![[assets/*.svg]])
```

- The **id** is the mathematics: it changes exactly when the Statement
  changes. Proof, Notes, links' display text, filenames — none affect it.
- **Names describe content** (`thm-classification-free-product`), never a
  source's numbering. Renaming is free (update inlinks); identity is the id.

## 1b · Pools

The vault holds one curated pool per body of mathematics it is building —
each a directory named `<Name>Hypergraph` — beside the raw `cardpool/`.
`tools/pools.py` is the single declaration; every tool reads it, so a new pool
is one line there.

- **Which pool a card belongs to**: the one it would still make sense in if
  the others vanished. Boundary cases can be left where they land — the id
  hashes the Statement, and a wikilink resolves by filename, so moving a card
  between pools changes neither its identity nor any link to it.
- **Pools do not partition the graph.** Cards cite across pools freely; that
  is the point of a second pool rather than a second vault. When two bodies of
  mathematics share no cards, no sources and no raw material, they are two
  vaults — the pool mechanism is for what is genuinely shared.
- **An edge lives with its SOURCE.** It is the source's assertion that its
  statement or proof consumes the target, and the target may well be in
  another pool.

## 2 · Edges

One file per edge, filed under `edges/<kind>/`, named `<source>→<target>`:

| kind | meaning | witnessed by |
|---|---|---|
| `uses` | the source's **proof** consumes the target result | a `[[link]]` in the Proof |
| `depends` | the source's **statement** builds on the target result | a `[[link]]` in the Statement |
| `references` | the target is a **definition** the source's text invokes | a `[[link]]` anywhere in Statement/Proof |

- **Text-mirror rule**: every edge is witnessed by a link and every link
  demands an edge — no phantom edges, no silent citations (`edge_lint`).
- **Exact-match rule**: an edge's target states *precisely* what the source
  consumes. If the available card proves something adjacent, insert the
  missing statement as its own card between them.
- An edge's id is `sha256(kind : source-id : target-id)` — it changes
  exactly when the relation or either endpoint's mathematics changes.

## 3 · Status: the five states of a statement

Every atom that can owe a proof carries a `status:` property, computed by
`tools/frontier.py` and never written by hand.

| status | definition | canvas |
|---|---|---|
| `debt` | no `## Proof` section, and nothing standing in for one | red |
| `open` | proof present, but the Statement/Proof cites at least one raw-pool card | magenta |
| `cited` | no `## Proof` section, but `cited:` names where in the literature it is proved | grey |
| `formal` | no `## Proof` section, but every `lean:` entry resolves and is `state: proven` | green |
| `proved` | proof present and every citation stays inside the clean pool, or is a declared ground notion | type colour |

Transitions: `debt` → (write the proof) → `open` or `proved`; `open` →
(graduate the pool cards it cites) → `proved`; `debt` → (name a
machine-checked counterpart) → `formal`; `debt` → (name the literature) →
`cited`.

`proved`, `formal` and `cited` are three different claims and are deliberately
not merged. `proved` says a reader can follow the argument on the card;
`formal` says a machine has checked it somewhere else and the card points at
where; `cited` says it is somebody else's theorem, consumed here and not
reproved.

`cited` is the network's boundary made explicit. Some statements an argument
consumes are somebody else's theorem and will not be reproved — Nash, Smale,
the Thom isomorphism. Left as prose inside a proof they are invisible: the
card reads `proved` and rests on something the network never states. As
`cited` cards they are nodes like any other, they can be pointed at, and the
question "what does this argument stand on" has a mechanical answer.
`tools/boundary_lint.py` enforces it: a named result appearing in a Statement
or Proof must resolve to a card or to a ground notion.

Definition, remark, conjecture and equation cards carry no status. The first
two have nothing to prove; a conjecture is named and not relied on, so
reporting it as a debt would say the argument rests on it; an equation asserts
nothing at all. Notes never affect status: a pool link in Notes is a soft
pointer, not a dependency.

## 4 · Where a concept may live

Every mathematical notion is in exactly one of three places:

1. **Definition card** (`atoms/definitions/`) — defines and *only* defines;
   a definition card never carries a theorem.
2. **Fact card** — any true statement, however small
   ($\pi_1(S^3/\Gamma) \cong \Gamma$), is a lemma/proposition with its
   own proof and id; facts
   are never smuggled into definitions or asides.
3. **Ground notion** — a declared primitive, listed in
   [[notation]] § Ground notions.

Anything in none of the three is an undeclared debt.

## 5 · Language

- **Statement and Proof are mathematics only** — no author names, no
  cf./see, no chapter pointers, no bibliography (`noise_lint`); prose in
  Let/Then form; key terms link their definition cards at first occurrence.
  A link alias must contain no math (`$…$` in an alias renders raw) — put
  the link on a plain word: `$S^2$-[[def-s2-bundle-over-s1|bundle]]`.
- **[[notation]] is normative**: one name and one symbol per concept,
  registered at graduation time.
- Statement templates: displayed formula (classification), itemized list
  (reassembly), enumerated conclusions (surgery flow). Proof styles:
  numbered steps for linear derivations, bold part headings for proofs in
  named parts, a single paragraph for one-move proofs; always end $\square$.
- **Every concept links at first occurrence.** In a Statement or Proof, a
  term with a definition card carries a `[[link]]` the first time it
  appears; later bare repeats in the same section are fine. `tools/term_lint.py`
  lists candidates (advisory — it cannot judge compounds).
- **A citation must be supported.** A proof cites `[[card]]` together with
  its *instantiation*: which objects here play the cited statement's data,
  and why its hypotheses hold at this point of the argument. What the
  citation yields is then *displayed* as a formula or stated symbolically
  — never paraphrased loosely. Prose that narrates ("the flow is repaired
  and continues") without a supported citation behind it is a defect.

## 6 · Growth

The graph grows by **graduation** from `cardpool/` (see FRONTIER.md for
proof debts and the citation frontier): refine the statement, name it by
content, wire the edges, mark the pool original `graduated: <stem>`.
Checks, all of which must print clean:

```
python3 tools/assign_ids.py     ids (idempotent)
python3 tools/render_lint.py    tex→Obsidian rendering
python3 tools/noise_lint.py     no bibliographic noise in the mathematics
python3 tools/edge_lint.py      edges ⇔ text
```
