#!/usr/bin/env python3
"""Generate PDF: Bridging Informal and Formal Mathematics."""

from reportlab.lib.pagesizes import letter
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.units import inch
from reportlab.lib.colors import HexColor
from reportlab.lib.enums import TA_CENTER, TA_JUSTIFY
from reportlab.platypus import (
    SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle,
    PageBreak, HRFlowable
)

OUTPUT = "/Users/moqian/hessenberg-digraphs/paper/informal_formal_bridge.pdf"

doc = SimpleDocTemplate(
    OUTPUT, pagesize=letter,
    leftMargin=1*inch, rightMargin=1*inch,
    topMargin=1*inch, bottomMargin=1*inch
)

styles = getSampleStyleSheet()

# Custom styles
styles.add(ParagraphStyle(
    'PaperTitle', parent=styles['Title'],
    fontSize=18, leading=22, spaceAfter=6, alignment=TA_CENTER
))
styles.add(ParagraphStyle(
    'Subtitle', parent=styles['Normal'],
    fontSize=11, leading=14, alignment=TA_CENTER,
    textColor=HexColor('#555555'), spaceAfter=20
))
styles.add(ParagraphStyle(
    'SectionHead', parent=styles['Heading1'],
    fontSize=14, leading=17, spaceBefore=18, spaceAfter=8,
    textColor=HexColor('#1a1a2e')
))
styles.add(ParagraphStyle(
    'SubHead', parent=styles['Heading2'],
    fontSize=12, leading=15, spaceBefore=12, spaceAfter=6,
    textColor=HexColor('#16213e')
))
styles.add(ParagraphStyle(
    'Body', parent=styles['Normal'],
    fontSize=10, leading=13, alignment=TA_JUSTIFY, spaceAfter=6
))
styles.add(ParagraphStyle(
    'SmallMono', parent=styles['Normal'],
    fontName='Courier', fontSize=8.5, leading=11, spaceAfter=4,
    leftIndent=20
))
styles.add(ParagraphStyle(
    'TableCell', parent=styles['Normal'],
    fontSize=8.5, leading=11
))
styles.add(ParagraphStyle(
    'Caption', parent=styles['Normal'],
    fontSize=9, leading=12, alignment=TA_CENTER,
    textColor=HexColor('#444444'), spaceBefore=4, spaceAfter=12
))

BLUE = HexColor('#1a1a2e')
LIGHT_BLUE = HexColor('#e8eaf6')
GREEN = HexColor('#2e7d32')
RED = HexColor('#c62828')
GRAY = HexColor('#f5f5f5')

story = []

# ── Title ──
story.append(Paragraph(
    "Bridging Informal and Formal Mathematics", styles['PaperTitle']))
story.append(Paragraph(
    "Digraphs of Real Orthogonal Upper Hessenberg Matrices", styles['Subtitle']))
story.append(Paragraph(
    "A Dual-Track Research Project with Lean 4 Verification and Knowledge Network Visualization",
    styles['Subtitle']))
story.append(HRFlowable(width="80%", thickness=1, color=BLUE, spaceAfter=16))

# ── Abstract ──
story.append(Paragraph("<b>Abstract</b>", styles['SubHead']))
story.append(Paragraph(
    "This document presents a dual-track mathematical research project that studies the support "
    "digraphs of real orthogonal upper Hessenberg matrices. The project pairs an informal LaTeX "
    "paper containing traditional proofs with a formal Lean 4 verification of the combinatorial "
    "results, achieving 95.7% theorem coverage (22 of 23 statements proved). A knowledge network "
    "of 101 atoms and 268 edges, visualized through Astrolabe, explicitly links informal and "
    "formal content, providing a navigable map of the mathematics across both representations.",
    styles['Body']))
story.append(Spacer(1, 12))

# ── 1. Introduction ──
story.append(Paragraph("1. Introduction", styles['SectionHead']))
story.append(Paragraph(
    "An <i>upper Hessenberg matrix</i> Q is a square matrix satisfying q<sub>ij</sub> = 0 "
    "whenever i > j + 1. The <i>support digraph</i> D(Q) encodes the zero/nonzero pattern of Q "
    "as a directed graph: vertex set {1, ..., n} with an arc (i, j) whenever q<sub>ij</sub> is nonzero. "
    "When Q is additionally real and orthogonal, a canonical <i>Givens factorization</i> "
    "parameterizes Q by an <i>active set</i> S, a subset of {1, ..., n-1}, yielding a purely "
    "combinatorial digraph model D<sub>n</sub>(S).",
    styles['Body']))
story.append(Paragraph(
    "This project pursues the mathematics along two parallel tracks: an informal paper written in "
    "LaTeX containing human-readable proofs, and a formal verification in Lean 4 (with Mathlib) "
    "that machine-checks the combinatorial results. A third artifact, an Astrolabe knowledge "
    "network, explicitly links theorems, definitions, and proofs across both sources.",
    styles['Body']))

# ── 2. The Informal Mathematics ──
story.append(Paragraph("2. The Informal Mathematics", styles['SectionHead']))
story.append(Paragraph(
    "The LaTeX paper (<font face='Courier' size='9'>paper/main.tex</font>, ~500 lines) develops "
    "the theory in five sections:",
    styles['Body']))

sections_data = [
    ["Section", "Content"],
    ["1-2", "Matrix-theoretic foundations: upper Hessenberg and orthogonal definitions, "
            "sign-equivalence, Givens rotations, canonical factorization (Theorem 4)"],
    ["3", "The combinatorial digraph model D_n(S): arc decomposition into spine arcs "
          "{(k+1, k)} and overlay arcs {(i, j) : i in R(S), j in C(n,S), i <= j}; "
          "connectivity; unique directed Hamilton cycle (Lemma 8)"],
    ["4", "Structural rigidity: degree formulas (Prop 9), isomorphism rigidity for "
          "|S| >= 2 (Theorem 10), singleton isomorphism classification (Lemma 11), "
          "enumeration formula 2^(n-1) - floor((n-1)/2) (Theorem 12)"],
    ["5", "Loopless digraphs: loop characterization (Lemma 13), loopless iff no "
          "consecutive elements in S (Cor 14), loopless count fib(n-1) - floor((n-3)/2) "
          "(Theorem 15), explicit examples for n = 5"],
]

t = Table(sections_data, colWidths=[0.6*inch, 5.0*inch])
t.setStyle(TableStyle([
    ('BACKGROUND', (0, 0), (-1, 0), BLUE),
    ('TEXTCOLOR', (0, 0), (-1, 0), HexColor('#ffffff')),
    ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
    ('FONTSIZE', (0, 0), (-1, -1), 9),
    ('LEADING', (0, 0), (-1, -1), 12),
    ('BACKGROUND', (0, 1), (-1, -1), GRAY),
    ('ROWBACKGROUNDS', (0, 1), (-1, -1), [GRAY, HexColor('#ffffff')]),
    ('GRID', (0, 0), (-1, -1), 0.5, HexColor('#cccccc')),
    ('VALIGN', (0, 0), (-1, -1), 'TOP'),
    ('TOPPADDING', (0, 0), (-1, -1), 4),
    ('BOTTOMPADDING', (0, 0), (-1, -1), 4),
    ('LEFTPADDING', (0, 0), (-1, -1), 6),
    ('RIGHTPADDING', (0, 0), (-1, -1), 6),
]))
story.append(t)
story.append(Paragraph("Table 1. Paper structure overview.", styles['Caption']))

story.append(Paragraph(
    "The core mathematical insight is that the active set S completely determines the digraph: "
    "the <i>active rows</i> R(S) = {1} union {k+1 : k in S} and <i>active columns</i> "
    "C(n, S) = S union {n} define the overlay arcs, while the spine arcs form the backbone "
    "(k+1, k) for all k. Every D<sub>n</sub>(S) contains exactly one directed Hamilton cycle: "
    "1 -> n -> (n-1) -> ... -> 2 -> 1.",
    styles['Body']))

# ── 3. The Formal Mathematics ──
story.append(Paragraph("3. The Formal Mathematics", styles['SectionHead']))
story.append(Paragraph(
    "The Lean 4 formalization (<font face='Courier' size='9'>lean/HessenbergDigraphs.lean</font>, "
    "887 lines) targets the combinatorial model from Sections 3-5 of the paper. The matrix-theoretic "
    "foundations (Sections 1-2) remain informal due to the infrastructure requirements for linear "
    "algebra over the reals in Lean/Mathlib.",
    styles['Body']))

story.append(Paragraph("3.1 Core Definitions in Lean", styles['SubHead']))
story.append(Paragraph(
    "<font face='Courier' size='9'>"
    "def R (S : Finset (Fin n)) : Finset (Fin n)  -- active rows<br/>"
    "def C (n : Nat) (S : Finset (Fin n)) : Finset (Fin n)  -- active columns<br/>"
    "def Arc (S : Finset (Fin n)) (i j : Fin n) : Prop  -- arc relation<br/>"
    "def Loop (S : Finset (Fin n)) (v : Fin n) : Prop  -- loop predicate<br/>"
    "def ValidS (S : Finset (Fin n)) : Prop  -- S subset {1,...,n-1}<br/>"
    "def DGraphIso (S S' : Finset (Fin n)) (sigma : Fin n -> Fin n) : Prop<br/>"
    "</font>",
    styles['Body']))

story.append(Paragraph("3.2 Verification Statistics", styles['SubHead']))

stats_data = [
    ["Metric", "Value"],
    ["Total theorems/lemmas", "23"],
    ["Formally proved", "22"],
    ["Remaining sorry", "1 (rigid, Theorem 10)"],
    ["Proof coverage", "95.7%"],
    ["Lines of Lean code", "887"],
    ["Lean version", "v4.28.0"],
    ["Mathlib version", "v4.28.0"],
    ["Development rounds", "2 (Aristotle AI-assisted)"],
]
t2 = Table(stats_data, colWidths=[2.2*inch, 3.4*inch])
t2.setStyle(TableStyle([
    ('BACKGROUND', (0, 0), (-1, 0), BLUE),
    ('TEXTCOLOR', (0, 0), (-1, 0), HexColor('#ffffff')),
    ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
    ('FONTSIZE', (0, 0), (-1, -1), 9),
    ('LEADING', (0, 0), (-1, -1), 12),
    ('ROWBACKGROUNDS', (0, 1), (-1, -1), [GRAY, HexColor('#ffffff')]),
    ('GRID', (0, 0), (-1, -1), 0.5, HexColor('#cccccc')),
    ('TOPPADDING', (0, 0), (-1, -1), 3),
    ('BOTTOMPADDING', (0, 0), (-1, -1), 3),
    ('LEFTPADDING', (0, 0), (-1, -1), 6),
]))
story.append(t2)
story.append(Paragraph("Table 2. Formalization statistics.", styles['Caption']))

# ── 4. Correspondence Table ──
story.append(Paragraph("4. Informal-Formal Correspondence", styles['SectionHead']))
story.append(Paragraph(
    "The following table maps each paper result to its Lean counterpart, showing the verification "
    "status. A checkmark indicates a complete, sorry-free proof; a cross indicates a remaining gap.",
    styles['Body']))

# Use Paragraph objects for wrapping
def tc(text):
    return Paragraph(text, styles['TableCell'])

corr_data = [
    [tc("<b>Paper</b>"), tc("<b>Result</b>"), tc("<b>Lean Name</b>"), tc("<b>Status</b>")],
    [tc("Thm 7"), tc("Digraph model D<sub>n</sub>(S)"), tc("<font face='Courier'>R, C, Arc</font>"), tc("<font color='#2e7d32'><b>Defined</b></font>")],
    [tc("Lem 8"), tc("Unique Hamilton cycle"), tc("<font face='Courier'>hcycle_subset</font>"), tc("<font color='#ef6c00'><b>Partial</b></font>")],
    [tc("Prop 9"), tc("Degree formulas"), tc("<font face='Courier'>outDeg_one, inDeg_n</font>"), tc("<font color='#2e7d32'><b>Proved</b></font>")],
    [tc("Thm 10"), tc("Rigidity (|S| >= 2)"), tc("<font face='Courier'>rigid</font>"), tc("<font color='#c62828'><b>Sorry</b></font>")],
    [tc("Lem 11"), tc("Singleton isomorphism"), tc("<font face='Courier'>singleton_iso,<br/>singleton_iso_unique</font>"), tc("<font color='#2e7d32'><b>Proved</b></font>")],
    [tc("Thm 12"), tc("Count: 2<super>n-1</super> - floor((n-1)/2)"), tc("<font face='Courier'>count_formula</font>"), tc("<font color='#2e7d32'><b>Proved</b></font>")],
    [tc("Lem 13"), tc("Loop characterization"), tc("<font face='Courier'>loop_iff_mem_R_and_C</font>"), tc("<font color='#2e7d32'><b>Proved</b></font>")],
    [tc("Cor 14"), tc("Loopless iff no consec."), tc("<font face='Courier'>loopless_iff</font>"), tc("<font color='#2e7d32'><b>Proved</b></font>")],
    [tc("Thm 15"), tc("Loopless count: fib(n-1) - floor((n-3)/2)"), tc("<font face='Courier'>count_loopless_formula</font>"), tc("<font color='#2e7d32'><b>Proved</b></font>")],
]

t3 = Table(corr_data, colWidths=[0.6*inch, 1.8*inch, 2.0*inch, 0.8*inch])
t3.setStyle(TableStyle([
    ('BACKGROUND', (0, 0), (-1, 0), BLUE),
    ('TEXTCOLOR', (0, 0), (-1, 0), HexColor('#ffffff')),
    ('FONTSIZE', (0, 0), (-1, -1), 9),
    ('LEADING', (0, 0), (-1, -1), 12),
    ('ROWBACKGROUNDS', (0, 1), (-1, -1), [GRAY, HexColor('#ffffff')]),
    ('GRID', (0, 0), (-1, -1), 0.5, HexColor('#cccccc')),
    ('VALIGN', (0, 0), (-1, -1), 'MIDDLE'),
    ('TOPPADDING', (0, 0), (-1, -1), 4),
    ('BOTTOMPADDING', (0, 0), (-1, -1), 4),
    ('LEFTPADDING', (0, 0), (-1, -1), 4),
    ('RIGHTPADDING', (0, 0), (-1, -1), 4),
]))
story.append(t3)
story.append(Paragraph(
    "Table 3. Theorem correspondence between informal paper and Lean 4 formalization.",
    styles['Caption']))

# ── 5. The Rigidity Gap ──
story.append(Paragraph("5. The Rigidity Gap", styles['SectionHead']))
story.append(Paragraph(
    "The single remaining <font face='Courier' size='9'>sorry</font> in the formalization is "
    "Theorem 10 (<font face='Courier' size='9'>rigid</font>): if |S| >= 2, then "
    "D<sub>n</sub>(S) isomorphic to D<sub>n</sub>(S') implies S = S'.",
    styles['Body']))
story.append(Paragraph("<b>What is proved:</b>", styles['Body']))
story.append(Paragraph(
    "The key helper <font face='Courier' size='9'>fixes_n_implies_id</font> is fully verified: "
    "if an isomorphism sigma fixes vertex n (i.e., sigma(n) = n), then sigma is the identity "
    "and S = S'. Additional helpers include "
    "<font face='Courier' size='9'>backward_arc_is_spine</font>, "
    "<font face='Courier' size='9'>cut_lemma</font>, "
    "<font face='Courier' size='9'>inDeg_mem_S</font>, and "
    "<font face='Courier' size='9'>vertex_one_arcs_to_all_C</font>.",
    styles['Body']))
story.append(Paragraph("<b>What remains:</b>", styles['Body']))
story.append(Paragraph(
    "The gap is showing that <i>any</i> isomorphism of D<sub>n</sub>(S) must fix vertex n when "
    "|S| >= 2. The paper's argument proceeds by observing that automorphisms act as cyclic "
    "rotations of the unique Hamilton cycle, and the in-degree sequence has a unique maximum at "
    "a specific vertex, forcing any rotation to be the identity. Formalizing this cyclic rotation "
    "argument is the remaining challenge.",
    styles['Body']))

# ── 6. Knowledge Network ──
story.append(Paragraph("6. The Knowledge Network", styles['SectionHead']))
story.append(Paragraph(
    "The project includes an Astrolabe knowledge network "
    "(<font face='Courier' size='9'>.astrolabe/astrolabe.json</font>) that explicitly links "
    "informal and formal content. The network contains:",
    styles['Body']))

net_data = [
    ["Component", "Count", "Description"],
    ["Atoms", "101", "Theorems, definitions, proofs from both tex and lean sources"],
    ["Edges", "268", "Dependencies, proof links, cross-source correspondences"],
    ["Sources", "2", "LaTeX paper (tex) and Lean formalization (lean)"],
]
t4 = Table(net_data, colWidths=[1.2*inch, 0.6*inch, 3.8*inch])
t4.setStyle(TableStyle([
    ('BACKGROUND', (0, 0), (-1, 0), BLUE),
    ('TEXTCOLOR', (0, 0), (-1, 0), HexColor('#ffffff')),
    ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
    ('FONTSIZE', (0, 0), (-1, -1), 9),
    ('LEADING', (0, 0), (-1, -1), 12),
    ('ROWBACKGROUNDS', (0, 1), (-1, -1), [GRAY, HexColor('#ffffff')]),
    ('GRID', (0, 0), (-1, -1), 0.5, HexColor('#cccccc')),
    ('TOPPADDING', (0, 0), (-1, -1), 3),
    ('BOTTOMPADDING', (0, 0), (-1, -1), 3),
    ('LEFTPADDING', (0, 0), (-1, -1), 6),
]))
story.append(t4)
story.append(Paragraph("Table 4. Knowledge network components.", styles['Caption']))

story.append(Paragraph(
    "The network supports multiple views: a <b>ReadView</b> for navigating the paper with "
    "clickable theorem blocks, a <b>NetworkView</b> for visualizing dependencies between "
    "informal and formal mathematics, and <b>Analytics</b> including PageRank centrality, "
    "community detection, and DAG depth analysis. Edge types include proof dependencies "
    "(which lemma uses which), statement-to-proof links, and cross-source correspondences "
    "(paper theorem to Lean theorem).",
    styles['Body']))

# ── 7. Methodology ──
story.append(Paragraph("7. Dual-Track Methodology", styles['SectionHead']))
story.append(Paragraph(
    "The project demonstrates a reproducible methodology for mathematical research that "
    "bridges informal and formal reasoning:",
    styles['Body']))
story.append(Paragraph(
    "<b>1. Write informal mathematics first.</b> The LaTeX paper develops the full theory "
    "including matrix-theoretic foundations that are difficult to formalize.",
    styles['Body']))
story.append(Paragraph(
    "<b>2. Formalize the combinatorial core.</b> The Lean 4 file targets the results most "
    "amenable to formalization (Sections 3-5), leaving continuous/analytic arguments informal.",
    styles['Body']))
story.append(Paragraph(
    "<b>3. AI-assisted proving.</b> Two rounds of Aristotle (AI proof assistant) brought "
    "coverage from 19/21 to 22/23, demonstrating the effectiveness of iterative AI collaboration.",
    styles['Body']))
story.append(Paragraph(
    "<b>4. Link with a knowledge network.</b> The Astrolabe graph connects every theorem, "
    "definition, and proof across both sources, making the informal-formal correspondence "
    "explicit and navigable.",
    styles['Body']))

# ── 8. Conclusion ──
story.append(Paragraph("8. Conclusion", styles['SectionHead']))
story.append(Paragraph(
    "This project demonstrates that informal and formal mathematics are not competing approaches "
    "but complementary layers of the same intellectual structure. The informal paper provides "
    "intuition, motivation, and continuous-mathematics foundations; the Lean formalization "
    "provides machine-checked certainty for the combinatorial core; and the knowledge network "
    "makes the correspondence between them explicit. With 95.7% of theorems formally verified "
    "and a single well-characterized gap remaining, the project illustrates both the power and "
    "the current boundaries of formal verification in mathematical research.",
    styles['Body']))

story.append(Spacer(1, 20))
story.append(HRFlowable(width="60%", thickness=0.5, color=HexColor('#999999'), spaceAfter=8))
story.append(Paragraph(
    "<i>Project repository: hessenberg-digraphs | "
    "Author: Simone Severini (University College London)</i>",
    ParagraphStyle('Footer', parent=styles['Normal'], fontSize=8, alignment=TA_CENTER,
                   textColor=HexColor('#888888'))))

# Build
doc.build(story)
print(f"PDF generated: {OUTPUT}")
