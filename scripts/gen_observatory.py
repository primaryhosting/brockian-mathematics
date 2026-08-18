#!/usr/bin/env python3
"""Generate observatory/index.html from observatory/claims.json.

Self-contained static page — no build step beyond this script. Open in a browser
or serve from any static host.

Usage:
    python3 scripts/gen_claims.py && python3 scripts/gen_observatory.py
"""
from __future__ import annotations

import argparse
import html
import json
import os
from typing import Any


BADGE_CLASS = {
    "V3-LEAN-RUN": "badge-v3",
    "CONDITIONAL": "badge-cond",
    "CONJECTURE": "badge-conj",
    "DEFINITION": "badge-def",
    "V2-INDEP-COMPUTED": "badge-v2",
    "NOT-CLAIMED": "badge-no",
    "V0-PROSE": "badge-v0",
    "OPEN": "badge-open",
    "ARISTOTLE-PENDING": "badge-ari",
    "UNVERIFIED": "badge-bad",
    "UNMAPPED": "badge-bad",
    "UNKNOWN": "badge-bad",
}


def esc(s: Any) -> str:
    return html.escape("" if s is None else str(s), quote=True)


def badge_html(label: str) -> str:
    cls = BADGE_CLASS.get(label, "badge-bad")
    return f'<span class="badge {cls}">{esc(label)}</span>'


def claim_card(c: dict[str, Any]) -> str:
    decls = c.get("declarations") or []
    decl_rows = []
    for d in decls:
        axle = (d.get("axle") or {}).get("verdict", "")
        env = (d.get("axle") or {}).get("environment", "")
        src = d.get("source") or ""
        decl_rows.append(
            f"<tr>"
            f"<td><code>{esc(d.get('short'))}</code></td>"
            f"<td>{esc(d.get('register'))}</td>"
            f"<td><code>{esc(src)}</code></td>"
            f"<td>{esc(axle)} {esc(env)}</td>"
            f"</tr>"
        )
    decl_table = ""
    if decl_rows:
        decl_table = (
            "<table class='decls'><thead><tr>"
            "<th>Declaration</th><th>Register</th><th>Source</th><th>AXLE</th>"
            "</tr></thead><tbody>"
            + "".join(decl_rows)
            + "</tbody></table>"
        )
    elif c.get("missing_lean"):
        decl_table = (
            "<p class='warn'>Mapped Lean names not found in registry: "
            + esc(", ".join(c["missing_lean"]))
            + "</p>"
        )
    notes = f"<p class='notes'>{esc(c.get('notes'))}</p>" if c.get("notes") else ""
    return f"""
    <article class="claim" id="{esc(c['id'])}">
      <header>
        <span class="cid">{esc(c['id'])}</span>
        {badge_html(c.get('book_badge') or 'UNKNOWN')}
      </header>
      <h3>{esc(c.get('title'))}</h3>
      <p class="book">{esc(c.get('book'))}</p>
      {notes}
      {decl_table}
    </article>
    """


def render(doc: dict[str, Any]) -> str:
    s = doc.get("summary") or {}
    reg = s.get("registry") or {}
    by_status = s.get("by_status") or {}
    claims = doc.get("claims") or []

    # group
    order = [
        ("proved", "Proved (V3 / Lean-run)"),
        ("conditional", "Conditional schemas"),
        ("conjecture", "Named conjectures"),
        ("definition", "Definitions only"),
        ("aristotle", "Aristotle in flight"),
        ("open", "Open formalization targets"),
        ("not_claimed", "Explicitly not claimed"),
        ("empirical", "Empirical / V2"),
        ("prose", "Prose"),
        ("unmapped", "Unmapped (fix claim_map)"),
    ]
    groups: dict[str, list] = {k: [] for k, _ in order}
    for c in claims:
        st = c.get("status") or "unmapped"
        groups.setdefault(st, []).append(c)

    sections = []
    for key, title in order:
        items = groups.get(key) or []
        if not items:
            continue
        cards = "\n".join(claim_card(c) for c in items)
        sections.append(f"<section class='group'><h2>{esc(title)} "
                        f"<span class='count'>{len(items)}</span></h2>"
                        f"<div class='grid'>{cards}</div></section>")

    status_pills = " ".join(
        f"<span class='pill'>{esc(k)}: <b>{v}</b></span>"
        for k, v in sorted(by_status.items(), key=lambda kv: -kv[1])
    )
    reg_pills = " ".join(
        f"<span class='pill reg'>{esc(k)}: <b>{v}</b></span>"
        for k, v in sorted(reg.items())
    )

    charter = esc(doc.get("charter") or "")
    gen = esc((doc.get("generated_at") or ""))
    prog = esc(doc.get("program") or "Brockian")

    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8"/>
<meta name="viewport" content="width=device-width, initial-scale=1"/>
<title>Observatory — {prog}</title>
<style>
  :root {{
    --bg: #0f1218; --panel: #171c26; --text: #e8ecf4; --muted: #9aa3b5;
    --line: #2a3344; --v3: #1f8a4c; --cond: #b8860b; --conj: #6b5b95;
    --no: #8b2942; --ari: #2a6f97; --open: #5c6b7a; --def: #3d4f66;
  }}
  * {{ box-sizing: border-box; }}
  body {{
    margin: 0; font-family: "Iowan Old Style", "Palatino Linotype", Palatino, Georgia, serif;
    background: var(--bg); color: var(--text); line-height: 1.5;
  }}
  header.hero {{
    padding: 2.5rem 1.5rem 1.5rem; border-bottom: 1px solid var(--line);
    background: linear-gradient(180deg, #141a24 0%, var(--bg) 100%);
  }}
  header.hero h1 {{ margin: 0 0 0.35rem; font-weight: 600; letter-spacing: 0.02em; }}
  header.hero .sub {{ color: var(--muted); max-width: 48rem; }}
  header.hero .meta {{ margin-top: 1rem; color: var(--muted); font-size: 0.9rem; }}
  .pills {{ display: flex; flex-wrap: wrap; gap: 0.4rem; margin-top: 1rem; }}
  .pill {{
    font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
    font-size: 0.75rem; padding: 0.25rem 0.55rem; border: 1px solid var(--line);
    border-radius: 999px; background: var(--panel); color: var(--muted);
  }}
  .pill.reg {{ border-color: #3a4a30; color: #b5d4a8; }}
  .pill b {{ color: var(--text); }}
  main {{ max-width: 1100px; margin: 0 auto; padding: 1.5rem; }}
  .charter {{
    background: var(--panel); border: 1px solid var(--line); border-radius: 8px;
    padding: 1rem 1.25rem; color: var(--muted); white-space: pre-wrap;
    font-size: 0.95rem; margin-bottom: 2rem;
  }}
  section.group {{ margin-bottom: 2.5rem; }}
  section.group h2 {{
    font-size: 1.15rem; font-weight: 600; border-bottom: 1px solid var(--line);
    padding-bottom: 0.4rem; margin: 0 0 1rem;
  }}
  section.group h2 .count {{
    font-family: ui-monospace, monospace; font-size: 0.8rem; color: var(--muted);
    font-weight: 400; margin-left: 0.4rem;
  }}
  .grid {{ display: grid; gap: 1rem; }}
  article.claim {{
    background: var(--panel); border: 1px solid var(--line); border-radius: 8px;
    padding: 1rem 1.15rem;
  }}
  article.claim header {{
    display: flex; justify-content: space-between; align-items: center; gap: 0.75rem;
    margin-bottom: 0.35rem;
  }}
  .cid {{
    font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
    font-size: 0.8rem; color: #7eb8ff; letter-spacing: 0.03em;
  }}
  article.claim h3 {{ margin: 0.2rem 0 0.35rem; font-size: 1.05rem; font-weight: 600; }}
  .book {{ color: var(--muted); font-size: 0.88rem; margin: 0 0 0.5rem; }}
  .notes {{ color: #c5cddc; font-size: 0.9rem; margin: 0.4rem 0 0.75rem; }}
  .warn {{ color: #f0a0a0; font-size: 0.85rem; }}
  table.decls {{
    width: 100%; border-collapse: collapse; font-size: 0.8rem;
    font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
  }}
  table.decls th, table.decls td {{
    text-align: left; padding: 0.35rem 0.4rem; border-top: 1px solid var(--line);
    vertical-align: top;
  }}
  table.decls th {{ color: var(--muted); font-weight: 500; }}
  code {{ font-size: 0.85em; }}
  .badge {{
    font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
    font-size: 0.68rem; font-weight: 600; letter-spacing: 0.04em;
    padding: 0.2rem 0.45rem; border-radius: 4px; white-space: nowrap;
  }}
  .badge-v3 {{ background: var(--v3); color: #eafff0; }}
  .badge-cond {{ background: var(--cond); color: #1a1200; }}
  .badge-conj {{ background: var(--conj); color: #f3eeff; }}
  .badge-def {{ background: var(--def); color: #dce6f5; }}
  .badge-v2 {{ background: #2d5a7a; color: #e0f0ff; }}
  .badge-no {{ background: var(--no); color: #ffe8ee; }}
  .badge-v0 {{ background: #3a3a3a; color: #ddd; }}
  .badge-open {{ background: var(--open); color: #eef2f6; }}
  .badge-ari {{ background: var(--ari); color: #e8f6ff; }}
  .badge-bad {{ background: #5a1a1a; color: #ffd0d0; }}
  footer {{
    max-width: 1100px; margin: 0 auto; padding: 1rem 1.5rem 3rem;
    color: var(--muted); font-size: 0.85rem; border-top: 1px solid var(--line);
  }}
  a {{ color: #8ec7ff; }}
  nav.toc {{ margin: 1rem 0 2rem; }}
  nav.toc a {{
    display: inline-block; margin: 0.15rem 0.35rem 0.15rem 0;
    font-family: ui-monospace, monospace; font-size: 0.75rem;
    color: #8ec7ff; text-decoration: none; border: 1px solid var(--line);
    padding: 0.15rem 0.4rem; border-radius: 4px;
  }}
  nav.toc a:hover {{ background: var(--panel); }}
</style>
</head>
<body>
<header class="hero">
  <h1>Observatory</h1>
  <p class="sub">{prog} — public claim surface. Badges are derived from the
  AXLE-attested Lean registry (independent cloud re-check at lean-4.32.0 + axiom audit;
  local from-source lake build pending); they are never hand-painted.</p>
  <div class="pills">{reg_pills}</div>
  <div class="pills">{status_pills}</div>
  <p class="meta">Generated {gen} · from <code>registry/theorems.json</code> +
  <code>observatory/claim_map.yaml</code></p>
</header>
<main>
  <div class="charter">{charter}</div>
  <nav class="toc" aria-label="Claim index">
    {"".join(f'<a href="#{esc(c["id"])}">{esc(c["id"])}</a>' for c in claims)}
  </nav>
  {"".join(sections)}
</main>
<footer>
  <p>PROVED = sorry-free + axiom-clean + independent AXLE verification.
  CONDITIONAL = real implication under a named open hypothesis.
  CONJECTURE = named Prop container, not a theorem.
  NOT-CLAIMED = explicit open problem (twins / Goldbach global / RH).</p>
  <p>Regenerate: <code>python3 scripts/gen_claims.py && python3 scripts/gen_observatory.py</code></p>
</footer>
</body>
</html>
"""


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--claims", default="observatory/claims.json")
    ap.add_argument("--out", default="observatory/index.html")
    args = ap.parse_args()
    if not os.path.exists(args.claims):
        raise SystemExit(f"missing {args.claims}; run scripts/gen_claims.py first")
    doc = json.load(open(args.claims, encoding="utf-8"))
    html_out = render(doc)
    os.makedirs(os.path.dirname(args.out) or ".", exist_ok=True)
    open(args.out, "w", encoding="utf-8").write(html_out)
    print(f"observatory: {len(doc.get('claims') or [])} claims → {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
