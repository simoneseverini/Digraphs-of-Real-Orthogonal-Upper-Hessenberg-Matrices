/**
 * Hessenberg Digraph profile widget for Lean 4 Infoview.
 *
 * Four panels:
 * 1. Header + profile stats
 * 2. SVG digraph + matrix pattern (side by side)
 * 3. Degree table
 * 4. Theorem certificate checklist
 */

import * as React from "react";
const { useEffect, useRef } = React;
const h = React.createElement;

const fg = "var(--vscode-editor-foreground,#ccc)";
const bg = "var(--vscode-editor-background,#1e1e1e)";
const bdr = "var(--vscode-editorWidget-border,#444)";
const link = "var(--vscode-textLink-foreground,#0984e3)";

export default function HessenbergDigraph(props) {
  const { n, activeSet, activeRows, activeCols, arcs, spineArcs,
          overlayArcs, loops, degrees, isLoopless,
          totalClasses, looplessClasses, certificates } = props;

  const spineSet = new Set(spineArcs.map(a => a[0]+","+a[1]));
  const arcSet = new Set(arcs.map(a => a[0]+","+a[1]));
  const loopSet = new Set(loops);
  const setStr = "{" + activeSet.join(", ") + "}";
  const rowStr = "{" + activeRows.join(", ") + "}";
  const colStr = "{" + activeCols.join(", ") + "}";

  // ── SVG digraph ──
  const svgRef = useRef(null);
  useEffect(() => {
    if (!svgRef.current) return;
    const w = 300, ht = 300;
    const cx = w/2, cy = ht/2, radius = w * 0.34;
    const pos = {};
    for (let i = 1; i <= n; i++) {
      const a = -Math.PI/2 + ((i-1)/n) * 2 * Math.PI;
      pos[i] = { x: cx + radius*Math.cos(a), y: cy + radius*Math.sin(a) };
    }
    let svg = `<svg width="${w}" height="${ht}" xmlns="http://www.w3.org/2000/svg">`;
    svg += `<defs>`;
    for (const [id,col] of [["as","#666"],["ao","#0984e3"]]) {
      svg += `<marker id="${id}" viewBox="0 -5 10 10" refX="20" refY="0"
        markerWidth="5" markerHeight="5" orient="auto">
        <path d="M0,-5L10,0L0,5" fill="${col}"/></marker>`;
    }
    svg += `</defs>`;
    for (const [s,t] of arcs) {
      if (s===t) continue;
      const isS = spineSet.has(s+","+t);
      const col = isS ? "#666" : "#0984e3";
      const mk = isS ? "url(#as)" : "url(#ao)";
      const dash = isS ? "" : `stroke-dasharray="5,3"`;
      svg += `<line x1="${pos[s].x}" y1="${pos[s].y}" x2="${pos[t].x}" y2="${pos[t].y}"
        stroke="${col}" stroke-width="1.3" ${dash} marker-end="${mk}" opacity="0.7"/>`;
    }
    for (const v of loops) {
      const p = pos[v];
      svg += `<ellipse cx="${p.x}" cy="${p.y-20}" rx="9" ry="11"
        fill="none" stroke="#d63031" stroke-width="1.5"/>`;
    }
    for (let i = 1; i <= n; i++) {
      const p = pos[i], isL = loopSet.has(i);
      svg += `<circle cx="${p.x}" cy="${p.y}" r="11"
        fill="${bg}" stroke="${isL?"#d63031":"#2d3436"}" stroke-width="${isL?2.5:1.5}"/>`;
      svg += `<text x="${p.x}" y="${p.y+4}" text-anchor="middle"
        font-size="11" font-family="monospace" fill="${fg}">${i}</text>`;
    }
    const ly = ht-42;
    [["#666","","spine"],["#0984e3",`stroke-dasharray="5,3"`,"overlay"],
     ["#d63031","","loop"]].forEach(([c,d,l],idx) => {
      const y = ly+idx*14;
      svg += `<line x1="6" y1="${y}" x2="22" y2="${y}" stroke="${c}" stroke-width="2" ${d}/>`;
      svg += `<text x="26" y="${y+3}" font-size="9" fill="${fg}">${l}</text>`;
    });
    svg += `</svg>`;
    svgRef.current.innerHTML = svg;
  }, [n, arcs, spineArcs, loops]);

  // ── Matrix ──
  const cs = Math.min(24, Math.floor(200/n));
  const mRows = [];
  const hCells = [h("td",{key:"c",style:{width:cs,height:cs}})];
  for (let j=1;j<=n;j++) hCells.push(h("td",{key:"h"+j,
    style:{textAlign:"center",fontSize:"9px",fontFamily:"monospace",color:fg}},j));
  mRows.push(h("tr",{key:"hdr"},...hCells));
  for (let i=1;i<=n;i++) {
    const cells = [h("td",{key:"r"+i,
      style:{textAlign:"right",fontSize:"9px",fontFamily:"monospace",
        paddingRight:"3px",color:fg}},i)];
    for (let j=1;j<=n;j++) {
      const has = arcSet.has(i+","+j);
      const isS = spineSet.has(i+","+j);
      const isL = i===j && loopSet.has(i);
      let bg2 = "transparent";
      if (isL) bg2="#d63031"; else if (has&&isS) bg2="#666"; else if (has) bg2="#0984e3";
      cells.push(h("td",{key:i+","+j,title:has?`${i}→${j}`:"",
        style:{width:cs,height:cs,backgroundColor:bg2,
          border:`1px solid ${bdr}`,opacity:has?1:0.15}}));
    }
    mRows.push(h("tr",{key:"r"+i},...cells));
  }

  // ── Degree table ──
  const degRows = (degrees||[]).map(d =>
    h("tr",{key:d.vertex},
      h("td",{style:{padding:"1px 6px",textAlign:"center"}}, "v"+d.vertex),
      h("td",{style:{padding:"1px 6px",textAlign:"center"}}, d.outDeg),
      h("td",{style:{padding:"1px 6px",textAlign:"center"}}, d.inDeg)));

  // ── Certificates ──
  const certItems = (certificates||[]).map((c,i) =>
    h("div",{key:i,style:{marginLeft:"4px",marginBottom:"1px"}},
      h("span",{style:{color:"#00b894"}},"✓ "),
      h("span",{style:{color:link}},c.thmName),
      " — "+c.claim));

  // ── Layout ──
  const label = (text) => h("div",{style:{fontWeight:"bold",
    marginBottom:"4px",marginTop:"10px",fontSize:"11px",color:fg}},text);
  const dim = (text) => h("span",{style:{color:"#888",fontSize:"11px"}},text);

  // Count-only mode (empty activeSet = #hessenberg_count)
  const countOnly = activeSet.length === 0;

  if (countOnly) {
    return h("div",{style:{fontFamily:"monospace",fontSize:"11px",
      padding:"8px",color:fg}},
      h("div",{style:{fontWeight:"bold",fontSize:"15px",marginBottom:"8px"}},
        "Classification counts (n = "+n+")"),
      h("table",{style:{borderCollapse:"collapse",marginLeft:"4px"}},
        h("tbody",null,
          h("tr",null,h("td",null,"Total classes"),
            h("td",{style:{paddingLeft:"12px",fontWeight:"bold"}},totalClasses)),
          h("tr",null,h("td",null,"Loopless classes"),
            h("td",{style:{paddingLeft:"12px",fontWeight:"bold"}},looplessClasses))
        )),
      h("div",{style:{marginTop:"12px",paddingTop:"8px",
        borderTop:`1px solid ${bdr}`}},
        label("Correctness certificates"),
        ...certItems)
    );
  }

  return h("div",{style:{fontFamily:"monospace",fontSize:"11px",padding:"8px",
    color:fg}},

    // Title
    h("div",{style:{fontWeight:"bold",fontSize:"15px",marginBottom:"2px"}},
      "D",h("sub",null,n),"(",setStr,")"),
    h("div",{style:{marginBottom:"8px",color:"#888"}},
      arcs.length+" arcs  ·  "+spineArcs.length+" spine  ·  "+
      overlayArcs.length+" overlay  ·  "+
      loops.length+" loop"+(loops.length!==1?"s":"")),

    // Profile stats
    label("Profile"),
    h("table",{style:{borderCollapse:"collapse",marginLeft:"4px"}},
      h("tbody",null,
        h("tr",null,h("td",null,"n"),h("td",{style:{paddingLeft:"12px"}},n)),
        h("tr",null,h("td",null,"S"),h("td",{style:{paddingLeft:"12px"}},setStr)),
        h("tr",null,h("td",null,"|S|"),h("td",{style:{paddingLeft:"12px"}},
          activeSet.length)),
        h("tr",null,h("td",null,"R(S)"),h("td",{style:{paddingLeft:"12px"}},rowStr)),
        h("tr",null,h("td",null,"C(S)"),h("td",{style:{paddingLeft:"12px"}},colStr)),
        h("tr",null,h("td",null,"Loopless"),h("td",{style:{paddingLeft:"12px"}},
          isLoopless?"yes":"no")),
        h("tr",null,h("td",null,"Hamilton"),h("td",{style:{paddingLeft:"12px"}},
          "contained")),
        h("tr",null,h("td",null,"Iso classes"),h("td",{style:{paddingLeft:"12px"}},
          totalClasses," ",dim("(all)"),"  ",looplessClasses," ",dim("(loopless)")))
      )),

    // Graph + Matrix
    h("div",{style:{display:"flex",gap:"12px",flexWrap:"wrap",
      alignItems:"flex-start",marginTop:"8px"}},
      h("div",null, label("Digraph"), h("div",{ref:svgRef})),
      h("div",null, label("Support pattern"),
        h("table",{style:{borderCollapse:"collapse"}},
          h("tbody",null,...mRows)))),

    // Degrees
    label("Degree sequence"),
    h("table",{style:{borderCollapse:"collapse",marginLeft:"4px",
      border:`1px solid ${bdr}`}},
      h("thead",null,h("tr",null,
        h("th",{style:{padding:"2px 6px",borderBottom:`1px solid ${bdr}`}},"v"),
        h("th",{style:{padding:"2px 6px",borderBottom:`1px solid ${bdr}`}},"out"),
        h("th",{style:{padding:"2px 6px",borderBottom:`1px solid ${bdr}`}},"in"))),
      h("tbody",null,...degRows)),

    // Certificates
    h("div",{style:{marginTop:"10px",paddingTop:"8px",
      borderTop:`1px solid ${bdr}`}},
      label("Correctness certificates"),
      ...certItems)
  );
}
