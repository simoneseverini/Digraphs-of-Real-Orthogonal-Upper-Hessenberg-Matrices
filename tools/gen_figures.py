#!/usr/bin/env python3
r"""gen_figures.py — render the paper's tikzpicture environments to SVG.

Obsidian draws a ```tikz block only with a community plugin, and the vault has
to open on stock Obsidian. So a figure is a committed SVG, and this rebuilds
it: add the figure's \label here and re-run after editing the paper.

The source is paper/sections/*.tex, not the markdown: that is the version
that compiles into the PDF, so the vault's figure and the paper's figure are
the same picture rather than two drawings that have to be kept in step.

pdflatex → PDF → pdftocairo -svg. Text becomes paths, so the SVG renders
identically wherever it is opened and carries no font dependency.
"""
import pathlib, re, subprocess, sys, tempfile

V = pathlib.Path(__file__).resolve().parent.parent
# Inside the pool, not at the repository root: `vault-export.mjs` collects
# figures by walking the curated pool and inlines them into the published
# page. A figure beside it is not collected, and the embed degrades to its
# own filename in prose.
OUT = V / 'HessenbergHypergraph' / 'assets'
OUT.mkdir(parents=True, exist_ok=True)

PREAMBLE = r"""\documentclass[border=6pt]{standalone}
\usepackage{amsmath,amssymb}
\usepackage{tikz}
\usepackage{xcolor}
\usetikzlibrary{matrix,backgrounds,fit,positioning,arrows.meta,calc}
\begin{document}
"""

# (output stem, source file, the \label the figure carries)
FIGURES = [
    ('fig-support-digraph-example',    'sec-results.tex',  'fig:intro-example'),
    ('fig-d6-s24-anatomy',             'sec-results.tex',  'fig:digraph-anatomy'),
    ('fig-q6-s24-support-pattern',     'sec-results.tex',  'fig:matrix_pattern'),
    ('fig-d5-s2',                      'sec-results.tex',  'fig:D5S2'),
    ('fig-d5-s13',                     'sec-results.tex',  'fig:D5S13'),
]

FIGENV = re.compile(r'\\begin\{figure\}.*?\\end\{figure\}', re.S)
PIC = re.compile(r'\\begin\{tikzpicture\}.*?\\end\{tikzpicture\}', re.S)


def picture_for(tex, label):
    """The tikzpicture of the figure environment carrying this \\label."""
    src = (V / 'paper' / 'sections' / tex).read_text()
    for block in FIGENV.finditer(src):
        if f'\\label{{{label}}}' in block.group(0):
            pic = PIC.search(block.group(0))
            if pic:
                return pic.group(0)
    sys.exit(f'{label}: no tikzpicture found in {tex}')


fail = 0
for stem, tex, label in FIGURES:
    pic = picture_for(tex, label)
    with tempfile.TemporaryDirectory() as d:
        d = pathlib.Path(d)
        (d / 'f.tex').write_text(PREAMBLE + pic + '\n\\end{document}\n')
        r = subprocess.run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error', 'f.tex'],
                           cwd=d, capture_output=True, text=True)
        if not (d / 'f.pdf').exists():
            tail = [l for l in r.stdout.splitlines() if l.startswith('!')][:3]
            print(f'FAIL  {stem}: {tail or "pdflatex produced no pdf"}')
            fail += 1
            continue
        # pdftocairo, not dvisvgm: dvisvgm's --pdf path needs Ghostscript or
        # mutool linked in, and this TeX Live ships neither.
        r = subprocess.run(['pdftocairo', '-svg', 'f.pdf', str(OUT / f'{stem}.svg')],
                           cwd=d, capture_output=True, text=True)
        svg = OUT / f'{stem}.svg'
        if not svg.exists():
            print(f'FAIL  {stem}: pdftocairo — {r.stderr.strip().splitlines()[-1:]}')
            fail += 1
            continue
        print(f'ok    {stem}.svg  ({svg.stat().st_size // 1024} KB, from {label})')

sys.exit(1 if fail else 0)
