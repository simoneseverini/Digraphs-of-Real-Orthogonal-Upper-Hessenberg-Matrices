/-
TikZ block extension for Verso, browser-direct rendering via TikZJax.

`@[code_block] tikz` accepts a TikZ source code block and emits a
`<script type="text/tikz">` tag in the rendered HTML. A bootstrap
`extraJs` snippet loads `tikzjax.js` + `fonts.css` from the TikZJax CDN
into every page's `<head>`, so the browser compiles the TikZ source to
SVG on demand.

This avoids any build-time pdflatex/poppler dependency: the canonical
form of each figure is its TikZ source, embedded verbatim in the page.
-/

import VersoManual

open Lean
open Std (HashSet)
open Verso Doc Genre.Manual Output Html
open Verso.Doc.Elab

namespace Paper

private def tikzjaxBootstrap : String :=
  "(function(){\n" ++
  "  var f = document.createElement('link');\n" ++
  "  f.rel = 'stylesheet';\n" ++
  "  f.href = 'https://tikzjax.com/v1/fonts.css';\n" ++
  "  document.head.appendChild(f);\n" ++
  "  var s = document.createElement('script');\n" ++
  "  s.src = 'https://tikzjax.com/v1/tikzjax.js';\n" ++
  "  document.head.appendChild(s);\n" ++
  "})();\n"

private def tikzCss : String :=
  ".tikz-figure { display: flex; justify-content: center; align-items: center; margin: 1.25em 0; }\n" ++
  ".tikz-figure svg { max-width: 100%; height: auto; }\n" ++
  /- Lean token-level syntax highlighting (Verso ships only the token classes, not colors). -/
  ".hl.lean .const.token { color: #2962a3; }\n" ++
  ".hl.lean .var.token { color: #006666; }\n" ++
  ".hl.lean .keyword.token { color: #7c4dff; font-weight: 600; }\n" ++
  ".hl.lean .literal.token { color: #c9540a; }\n" ++
  ".hl.lean .docstring { color: #4a4a4a; font-style: italic; }\n" ++
  /- Source-link icon next to {name} references — make the ✓ checkmark a clickable GitHub link. -/
  ".lean-src-link { color: #006400; text-decoration: none; margin-left: 0.15em; font-weight: bold; }\n" ++
  ".lean-src-link:hover { text-decoration: underline; }\n" ++
  /- Allow the page banner title to shrink/wrap instead of being clipped by the search box. -/
  ".header-title { font-size: 1.15rem !important; }\n" ++
  ".header-title h1 { text-wrap: wrap !important; font-size: inherit !important; line-height: 1.25 !important; }\n" ++
  /- Desktop TOC collapse: show the burger toggle (hidden by default outside mobile),
     and when its checkbox is checked, slide the sidebar off-screen and free the content. -/
  "@media screen and (min-width: 701px) {\n" ++
  "  #toggle-toc-click { display: inline-flex !important; cursor: pointer; box-sizing: content-box;\n" ++
  "    width: var(--verso-burger-width); height: var(--verso-burger-height); padding: 0.5rem;\n" ++
  "    position: fixed; left: 0.75rem; z-index: 100; flex-direction: column; justify-content: space-between;\n" ++
  "    top: calc((var(--verso-header-height) - var(--verso-burger-height) - 1rem) / 2); }\n" ++
  "  body:has(#toggle-toc:checked) #toc { transform: translateX(-105%); }\n" ++
  "  body:has(#toggle-toc:checked) .with-toc > main { padding-left: var(--verso--content-padding-x) !important; }\n" ++
  "  #toc, .with-toc > main { transition: transform 0.25s ease, padding-left 0.25s ease; }\n" ++
  "}\n"

block_extension Block.tikz (source : String) where
  data := Json.str source
  traverse _id _data _contents := pure none
  extraJs := { JS.mk tikzjaxBootstrap }
  extraCss := { CSS.mk tikzCss }
  toTeX := none
  toHtml :=
    some <| fun _ _ _ data _ => do
      let .str source := data
        | HtmlT.logError s!"TikZ block: expected string data, got {data.compress}"
          return .empty
      return Html.tag "div" #[("class", "tikz-figure")] <|
        Html.tag "script" #[("type", "text/tikz")] (Html.text (escape := false) source)

@[code_block]
def tikz : CodeBlockExpanderOf Unit
  | (), str => do
    let source := str.getString
    `(Verso.Doc.Block.other (Block.tikz $(quote source)) #[])

end Paper
