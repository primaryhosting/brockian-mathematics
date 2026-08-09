#!/usr/bin/env python3
"""observatory.py — one-glance status of the whole proof fleet across all pipelines.
Aggregates every ledger into observatory.json + observatory.md + a self-contained,
theme-aware observatory.html dashboard. Read-only."""
import collections
import html
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent
REPO = ROOT.parent


def load(p, d):
    p = ROOT / p if not str(p).startswith("/") else pathlib.Path(p)
    try:
        return json.loads(p.read_text())
    except Exception:  # noqa: BLE001
        return d


def gather():
    night = load("submitted_night.json", {})
    harvest = load("harvest_ledger.json", {})
    vstate = load("harvest_100/verify_state.json", {})
    best = load("best_proofs/manifest.json", {})
    domains = load(REPO / "registry" / "domains.json", {})
    reductions = load("reductions.json", {})
    lemmas = load("mined_lemmas/manifest.json", {})
    cross = load("cross_check.json", {})
    pr = load("pr_plan.json", {})

    sub_by_acct, sub_by_dom = collections.Counter(), collections.Counter()
    for t, v in night.items():
        for i in v.get("ids", []):
            sub_by_acct[i["account"]] += 1
        sub_by_dom[v.get("tier", "?").split("-")[-1]] += len(v.get("ids", []))
    submits = sum(sub_by_acct.values())
    proved = sum(1 for v in harvest.values() if v.get("verdict") == "PROVED")
    stopped = sum(1 for v in harvest.values() if v.get("verdict") == "STOPPED")
    return {
        "submitted": submits, "targets": len(night),
        "by_account": dict(sub_by_acct), "by_domain": dict(sub_by_dom),
        "harvested": len(harvest), "proved": proved, "stopped": stopped,
        "lake_verified": sum(1 for s in vstate.values() if s.get("compiles") is True),
        "kernel_trusted": sum(1 for s in cross.values() if s.get("trusted") is True),
        "best_proofs": len(best), "domains": len(domains),
        "reductions": sum(len(v) for v in reductions.values()),
        "mined_lemmas": sum(len(v.get("lemmas", [])) for v in lemmas.values()),
        "pr_eligible": pr.get("count", 0),
    }


def _bars(d, accent):
    if not d:
        return '<p class="muted">none yet</p>'
    m = max(d.values()) or 1
    rows = []
    for k, v in sorted(d.items(), key=lambda x: -x[1]):
        rows.append(f'<div class="bar"><span class="bl">{html.escape(str(k))}</span>'
                    f'<span class="bt"><i style="width:{100*v//m}%;background:{accent}"></i></span>'
                    f'<span class="bv">{v}</span></div>')
    return "".join(rows)


TILES = [("submitted", "submitted", "acc"), ("proved", "proved", "good"),
         ("lake_verified", "lake-verified", "good"), ("kernel_trusted", "kernel-trusted", "good"),
         ("best_proofs", "best (deduped)", "acc"), ("domains", "domain results", "acc"),
         ("reductions", "reductions", "warn"), ("mined_lemmas", "salvaged lemmas", "acc"),
         ("stopped", "stopped", "bad"), ("pr_eligible", "PR-ready", "good")]

STAGES = [("generate", "targets"), ("submit", "submitted"), ("harvest", "harvested"),
          ("verify", "lake_verified"), ("trust", "kernel_trusted"),
          ("catalogue", "domains"), ("publish", "pr_eligible")]


def render_html(s):
    tiles = "".join(
        f'<div class="tile"><div class="k">{lbl}</div>'
        f'<div class="v {tone}">{s.get(key,0)}</div></div>' for key, lbl, tone in TILES)
    flow = "".join(
        f'<div class="stage"><div class="sn">{name}</div><div class="sv">{s.get(src,0)}</div></div>'
        + ("" if i == len(STAGES) - 1 else '<div class="arrow">→</div>')
        for i, (name, src) in enumerate(STAGES))
    return f"""<style>
:root{{--bg:#f5f6fa;--panel:#fff;--ink:#151824;--muted:#5a6478;--line:#e4e7f0;
 --acc:#4b57d6;--good:#0f8a5f;--good-b:#e2f3ec;--warn:#a8620a;--warn-b:#f8ecd8;--bad:#c02a3f;--bad-b:#fbe4e7;
 --mono:ui-monospace,"SF Mono",Menlo,Consolas,monospace;--sans:system-ui,-apple-system,"Segoe UI",sans-serif;}}
@media(prefers-color-scheme:dark){{:root{{--bg:#0c0e15;--panel:#151926;--ink:#e9ecf5;--muted:#98a2ba;
 --line:#232838;--acc:#8f9bff;--good:#4fd6a0;--good-b:#123027;--warn:#e6a94e;--warn-b:#332610;--bad:#ff7b8c;--bad-b:#33141b;}}}}
:root[data-theme="light"]{{--bg:#f5f6fa;--panel:#fff;--ink:#151824;--muted:#5a6478;--line:#e4e7f0;--acc:#4b57d6;--good:#0f8a5f;--warn:#a8620a;--bad:#c02a3f;}}
:root[data-theme="dark"]{{--bg:#0c0e15;--panel:#151926;--ink:#e9ecf5;--muted:#98a2ba;--line:#232838;--acc:#8f9bff;--good:#4fd6a0;--warn:#e6a94e;--bad:#ff7b8c;}}
*{{box-sizing:border-box}}body{{margin:0;background:var(--bg);color:var(--ink);font-family:var(--sans);
 font-variant-numeric:tabular-nums;-webkit-font-smoothing:antialiased}}
.wrap{{max-width:1000px;margin:0 auto;padding:36px 22px 64px}}
.eyebrow{{font-family:var(--mono);font-size:11.5px;letter-spacing:.16em;text-transform:uppercase;color:var(--acc)}}
h1{{font-size:26px;font-weight:680;letter-spacing:-.02em;margin:.25em 0 .1em}}
.sub{{color:var(--muted);font-size:14px;margin:0}}
.tiles{{display:grid;grid-template-columns:repeat(5,1fr);gap:12px;margin-top:26px}}
@media(max-width:780px){{.tiles{{grid-template-columns:repeat(2,1fr)}}}}
.tile{{background:var(--panel);border:1px solid var(--line);border-radius:12px;padding:14px 16px}}
.tile .k{{font-family:var(--mono);font-size:10.5px;letter-spacing:.06em;text-transform:uppercase;color:var(--muted)}}
.tile .v{{font-size:30px;font-weight:680;letter-spacing:-.02em;margin-top:4px;font-family:var(--mono)}}
.v.good{{color:var(--good)}}.v.warn{{color:var(--warn)}}.v.bad{{color:var(--bad)}}.v.acc{{color:var(--ink)}}
h2{{font-size:12px;font-family:var(--mono);letter-spacing:.1em;text-transform:uppercase;color:var(--muted);margin:34px 0 12px}}
.cols{{display:grid;grid-template-columns:1fr 1fr;gap:20px}}@media(max-width:780px){{.cols{{grid-template-columns:1fr}}}}
.card{{background:var(--panel);border:1px solid var(--line);border-radius:12px;padding:16px 18px}}
.bar{{display:grid;grid-template-columns:120px 1fr 40px;align-items:center;gap:10px;margin:7px 0;font-size:13px}}
.bl{{font-family:var(--mono);font-size:12px;color:var(--muted);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}}
.bt{{height:10px;background:var(--line);border-radius:5px;overflow:hidden}}.bt i{{display:block;height:100%}}
.bv{{font-family:var(--mono);text-align:right}}
.flow{{display:flex;align-items:center;gap:8px;overflow-x:auto;padding:16px;background:var(--panel);
 border:1px solid var(--line);border-radius:12px}}
.stage{{text-align:center;min-width:82px}}.sn{{font-family:var(--mono);font-size:10.5px;letter-spacing:.05em;
 text-transform:uppercase;color:var(--muted)}}.sv{{font-family:var(--mono);font-size:22px;font-weight:680;margin-top:3px}}
.arrow{{color:var(--muted);font-size:18px}}
.muted{{color:var(--muted);font-size:13px}}
.foot{{margin-top:30px;color:var(--muted);font-size:12px;border-top:1px solid var(--line);padding-top:14px;font-family:var(--mono)}}
</style>
<div class="wrap">
 <div class="eyebrow">Aristotle proof fleet · autonomous</div>
 <h1>Prover-fleet observatory</h1>
 <p class="sub">Lean 4 / Mathlib proofs across both accounts — generate → submit → harvest → verify → trust → publish.</p>
 <div class="tiles">{tiles}</div>
 <h2>Pipeline throughput</h2>
 <div class="flow">{flow}</div>
 <div class="cols">
  <div><h2>Submissions by account</h2><div class="card">{_bars(s['by_account'],'var(--acc)')}</div></div>
  <div><h2>Submissions by domain</h2><div class="card">{_bars(s['by_domain'],'var(--good)')}</div></div>
 </div>
 <div class="foot">targets attempted {s['targets']} · harvested {s['harvested']} · proved {s['proved']} · stopped {s['stopped']}
  · verification trails proving (import-Mathlib tax). Read-only snapshot.</div>
</div>"""


def main():
    s = gather()
    (ROOT / "observatory.json").write_text(json.dumps(s, indent=1))
    (ROOT / "observatory.md").write_text("# Proof-fleet observatory\n\n"
                                         + "\n".join(f"- **{k}**: {v}" for k, v in s.items()))
    (ROOT / "observatory.html").write_text(render_html(s))
    print(json.dumps(s, indent=1))
    print("wrote observatory.json / .md / .html")


if __name__ == "__main__":
    main()
