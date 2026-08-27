# Aristotle Command Dashboard — Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Ship `aristotle/dashboard_build.py` (aggregator → `dashboard_data.json`) and a single-file HTML dashboard published as a Claude Artifact, per the approved spec.

**Spec (binding, read first):** `docs/superpowers/specs/2026-08-27-aristotle-dashboard-design.md` — all derivation rules (stage ordering, name join, registry restriction, multi-tier matrix, honesty rules) live there and override anything ambiguous here.

**Architecture:** Generator (pure read-only Python, stdlib-only) emits the data contract; a template HTML file with a `/*__DATA__*/` placeholder is rendered by substituting the JSON; the rendered file is published as an Artifact. Phase 2 (ACUTIS live page) consumes the same JSON — out of scope here.

**Tech Stack:** Python 3 stdlib + pytest 9 (repo already uses `tests/test_*.py`). Page: hand-rolled HTML/CSS/JS, zero external deps (Artifact CSP), inline SVG charts.

**Riemann decision (probed 2026-08-27):** Riemann Supabase has NO per-theorem dot-name table reachable with anon key (`proofs` = 405 prose-titled seeds, `solver_fleet_snapshot` = empty). Generator therefore emits `"riemann": null` + a warning `"riemann: no per-theorem table; publish path is phase 2"`. Do NOT attempt fuzzy matching against `proofs.title`. The page's Riemann section shows the honest empty state + static links (https://torus.riemannlab.com, /atlas).

## File structure

- Create: `aristotle/dashboard_build.py` — aggregator; `main()` writes `aristotle/dashboard_data.json`; pure functions importable for tests.
- Create: `tests/test_dashboard_build.py` — fixture-driven unit tests (no real data files).
- Create: `aristotle/dashboard_template.html` — full page with `/*__DATA__*/` placeholder.
- Create: `aristotle/render_dashboard.py` — 30-line substitution: template + data json + `--generated-at` stamp → `aristotle/dashboard.html` (gitignored output; template is committed).
- Modify: `.gitignore` — add `aristotle/dashboard.html`, `aristotle/dashboard_data.json` (generated artifacts stay out of git; ledger files already in repo).

## Chunk 1: Generator

### Task 1: dashboard_build.py with tests (TDD)

**Key function signatures** (all pure, unit-testable):

```python
def load_ledger(path) -> dict                 # uuid -> entry; tolerate extra fields
def domain_of(target: str) -> str             # "AdditiveComb.x" -> "AdditiveComb"; no dot -> "(root)"
def mangle(target: str) -> str                # dots -> underscores, ".lean" appended by callers
def build_targets(ledger, axle, best_files, registry_names, inflight_ids) -> list[dict]
def build_funnel(targets, ledger) -> dict
def build_yield_matrix(ledger) -> list[dict]  # per (domain, tier); dedupe submissions per (target, tier)
def build_health(night_log_tail, submitted_night, ledger) -> dict
def build_warnings(...) -> list[str]
```

- [ ] **Step 1: Write failing tests** in `tests/test_dashboard_build.py` covering, with small inline fixture dicts (NOT real files):
  - dedup: 3 submissions of one target → 1 row, `submissions: 3`, account split correct.
  - stage ordering: PROVED+STOPPED mixed → `candidate`; with axle `verified: true` → `verified`; `verified: false` → `verify_failed`; `verified: null` → stage falls back to `selected` (if in best_files) AND a warning is emitted; target in registry_names → `attested`; night-submit ID absent from ledger → target row `in_flight`.
  - name join: `A.b.c` matches key `A_b_c.lean`; orphan axle key (no target) → counted in warnings, excluded from funnel.
  - funnel: `axle_verified` counts joined targets only; `registry_attested` counts only dot-name-matched pipeline targets; nested-stage monotonicity (submissions ≥ unique ≥ candidates ≥ selected ≥ verified) asserted; registry>verified crossover → warning, not failure.
  - multi-tier: target under 2 tiers appears in both matrix cells; row `tiers` lists both.
  - missing file: `axle=None` → section null-safe, warning added, no exception.
- [ ] **Step 2:** `pytest tests/test_dashboard_build.py -v` → all FAIL (module missing).
- [ ] **Step 3:** Implement `aristotle/dashboard_build.py`. Constraints: stdlib only; read-only (never writes any input file); `main()` degrades per-section on missing/corrupt inputs (section→null + warning, exit 0); Lean previews: first 20 lines, ONLY for joined `verified: true` targets; `generated_at` passed via `--generated-at` arg or `datetime.now(timezone.utc)` at CLI layer only (keep pure functions time-free). Health: parse last 50 `night_submit.log` lines (`OK|FAIL ... (RATE)` format), count RATE in last 24h from log timestamps, account split, and stale-file warnings (solver_state mtime > 7d, harvest_report `-927` bug).
- [ ] **Step 4:** `pytest tests/test_dashboard_build.py -v` → all PASS. Also run repo suite guard: `pytest tests/ -x -q -k dashboard` stays green.
- [ ] **Step 5:** Commit (explicit paths only — NEVER `git add -A`): `git add aristotle/dashboard_build.py tests/test_dashboard_build.py && git commit --no-verify -m "feat(dashboard): aristotle dashboard data generator"`

### Task 2: Run on real data + ground-truth check

- [ ] **Step 1:** `python3 aristotle/dashboard_build.py` → writes `aristotle/dashboard_data.json`.
- [ ] **Step 2:** Verify against spec ground truth (small tolerance for pipeline drift since it runs live): submissions ≈ 7,271; unique ≈ 1,341; proved ≈ 6,747; stopped ≈ 524; selected ≈ 1,264 files → joined counts reported; axle_verified ≈ 1,012; registry_attested ≈ 194; riemann null; warnings include orphans + stale solver_state. Print the funnel and eyeball it. If any number is wildly off (>2% or wrong order of magnitude), STOP and debug — do not ship.
- [ ] **Step 3:** `.gitignore` additions; commit `.gitignore` only.

## Chunk 2: Page + publish

### Task 3: dashboard_template.html

Author with the **dataviz** skill (charts) and **artifact-design** skill (page calibration) loaded. Requirements (spec §Component 2 is binding):

- Single file, no external requests. Data injected at `/*__DATA__*/` as `const DATA = {...};`.
- Dual theme: `@media (prefers-color-scheme: dark)` + `:root[data-theme]` overrides; ≥4.5:1; min font 11px.
- Sections in order: (1) provenance funnel — horizontal SVG funnel with epistemic labels + the `PROVED ≠ attested` banner + non-nested-registry annotation (28 attested-without-pipeline-cert); (2) domain × tier heatmap, toggle verified/proved/stopped-rate, multi-tier footnote; (3) corpus ledger table — paged (100/page) + filters (domain/tier/stage/account dropdowns from data) + name search + column sort; (4) certificate drawer on row click — AXLE verdict/env/hash, 20-line preview (verified only), GitHub link `https://github.com/primaryhosting/brockian-mathematics/blob/<branch>/aristotle/best_proofs/<file>`, honest copy for candidate ("no independent certificate yet") and attested-without-cert ("attested via repo registry; no pipeline AXLE certificate"); (5) triage queue — unverified candidates ranked by tier then domain verified-rate desc, copyable next-25 list (`navigator.clipboard`); (6) pipeline health — recent events timeline, RATE count, account split, warnings list; (7) Riemann — empty state + links.
- Every section renders its empty state if its data slice is null. Wide content scrolls in its own container.

- [ ] **Step 1:** Write `aristotle/dashboard_template.html`.
- [ ] **Step 2:** Write `aristotle/render_dashboard.py` (substitute placeholder, fail loudly if placeholder missing or JSON invalid).
- [ ] **Step 3:** Render with real `dashboard_data.json` → `aristotle/dashboard.html`.
- [ ] **Step 4:** Commit template + renderer (explicit paths).

### Task 4: Eyes-on verify (no headless-only ship — hard rule)

- [ ] Open `aristotle/dashboard.html` in the real browser. Check: both themes, funnel numbers match `dashboard_data.json`, heatmap toggle, ledger filter/search/sort on real 1,341 rows (responsive, no jank), drawer for one verified + one candidate + one attested-without-cert target, triage copy button, health warnings visible, Riemann empty state. Fix and re-render until right.

### Task 5: Publish + wrap

- [ ] Publish rendered `dashboard.html` as Claude Artifact (favicon 📐, stable title "Aristotle Command Dashboard").
- [ ] Full test suite spot-check: `pytest tests/test_dashboard_build.py -q` green.
- [ ] Commit any remaining changes (explicit paths); update memory with artifact URL + refresh recipe (`dashboard_build.py` → `render_dashboard.py` → redeploy Artifact).

## Refresh recipe (document in commit message of Task 5)

```bash
cd ~/Projects/brockian-mathematics
python3 aristotle/dashboard_build.py && python3 aristotle/render_dashboard.py
# then: any Claude session redeploys aristotle/dashboard.html to the same Artifact URL
```
