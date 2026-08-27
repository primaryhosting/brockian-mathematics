# Aristotle Command Dashboard — Design

**Date:** 2026-08-27
**Status:** Draft for review
**Owner:** Chris Brock
**Phase 1:** Claude Artifact (snapshot, regenerable). **Phase 2:** live ACUTIS page (:18820) consuming the same data contract.

## Problem

The Aristotle conveyor has produced 7,271 submissions across ~2 months, but the outputs live in five JSON files, three log files, and a Markdown report with broken counters (`still proving: -927`). There is no single place to:

- **Sort** — browse the corpus by domain, campaign/tier, verdict, account.
- **Understand** — see the honest provenance funnel (Aristotle-internal `PROVED` is *not* the same as independently attested).
- **Steer** — decide which of ~5,500 unverified candidates to push through AXLE next, and which domains deserve the next submission wave.

## Ground truth (measured 2026-08-27)

| Stage | Count | Source |
|---|---|---|
| Submissions (all time) | 7,271 | `aristotle/harvest_ledger.json` |
| — Aristotle-internal `PROVED` | 6,747 | ledger `verdict` |
| — `STOPPED` | 524 | ledger `verdict` |
| Unique targets | 1,341 (dedupe on `target`) | ledger |
| Selected best proofs (Lean files) | 1,264 | `aristotle/best_proofs/*.lean` |
| AXLE verification results | 1,277 | `aristotle/axle_verify.json` (`verified`, `environment`, `hash`) |
| Registry (attestation-derived) | `registry/theorems.json` (`generated_from: "AXLE attestations"`) | registry |
| Night-submit tracking | 654 | `aristotle/submitted_night.json` |
| Solver-state (STALE — all IDLE, 3 weeks old) | 2,170 | `aristotle/solver_state.json` |

Ledger container is a **dict keyed by project UUID** (not a list). Entry shape: `{target, account (admin|chris), verdict, tier}`; ~1,181 entries carry extra `origin`/`project_name` fields. Targets are namespaced (`Brockian.*`, `AdditiveComb.*`, `Phys.*`, …); the namespace prefix is the **domain** dimension. Unique targets: **1,341**.

**There is no separate "wave" dimension.** The `tier` field holds the campaign labels (`FRONTIER-wave2`, `DOMAIN-math`, `A1-discharge-literature`, `B-conjecture`, …) — the `[FRONTIER-wave2]` tags in `harvest_report.md` are the same values. The dashboard's second dimension is **tier** (labeled "campaign/tier" in the UI). 91 of 1,341 targets were submitted under more than one tier; a target's ledger row lists **all** its tiers, and the yield matrix counts it in **each** (domain, tier) cell it appeared under (submissions deduped per (target, tier)); the matrix carries a footnote that multi-tier targets appear in multiple cells, so cell sums exceed unique totals.

## Architecture

Two components, one data contract:

```
aristotle/*.json + logs ──> aristotle/dashboard_build.py ──> aristotle/dashboard_data.json
                                                                    │
                                              Phase 1: rendered into single-file HTML → Claude Artifact
                                              Phase 2: served raw to ACUTIS route (same schema)
```

### Component 1 — `aristotle/dashboard_build.py` (generator)

Pure read-only aggregator. Reads:

- `harvest_ledger.json`, `axle_verify.json`, `submitted_night.json`, `best_proofs/` (filenames + ~20-line previews, AXLE-verified targets only), `registry/theorems.json`, tail of `night_submit.log` (last 50 events, for health timeline).
- **Optionally** Riemann Supabase (via `RIEMANN_SUPABASE_URL`/`ANON_KEY` from vault): count + list of published theorem slugs, joined to targets. If env/network absent → section emits `"riemann": null` and the page shows an honest empty state ("not queried"), never zeros.

Emits `aristotle/dashboard_data.json`:

```jsonc
{
  "generated_at": "…",                       // stamped by caller, not Date.now in-page
  "funnel": { "submissions": n, "unique_targets": n, "proved_candidates": n,
              "stopped": n, "selected_best": n, "axle_verified": n,
              "axle_failed": n, "registry_attested": n, "riemann_published": n|null },
  "targets": [ {                             // ONE ROW PER UNIQUE TARGET — the corpus ledger
      "target": "AdditiveComb.cauchy_davenport_Z5",
      "domain": "AdditiveComb", "tiers": ["FRONTIER-wave2"],
      "submissions": 10, "accounts": {"admin": 5, "chris": 5},
      "verdicts": {"PROVED": 9, "STOPPED": 1},
      "stage": "attested|verified|verify_failed|selected|candidate|in_flight|stopped",
      "certificate": { "file": "…", "verified": true|false|null, "environment": "lean-4.32.2",
                       "hash": "…", "preview": "…first lines…",
                       "github_url": "https://github.com/primaryhosting/brockian-mathematics/blob/…" } | null,
      "riemann_published": true|false|null
  } ],
  "yield_matrix": [ {"domain": "…", "tier": "…", "unique": n, "proved_rate": x,
                     "verified_rate": x, "stopped_rate": x} ],
  "health": { "recent_events": [...], "rate_limit_count_24h": n,
              "account_split": {...}, "stale_files": ["solver_state.json (3w)"],
              "last_harvest_sync": "…" },
  "warnings": ["harvest_report counter bug (-927)", ...]
}
```

**Derivation rules (binding):**

- **Stage ordering** (max wins per target): `attested (6) > verified (5) > verify_failed (4) > selected (3) > candidate (2) > in_flight (1) > stopped (0)`. So a target with 9 PROVED + 1 STOPPED and no AXLE result = `candidate`. `verify_failed` = AXLE `verified: false` — surfaced, never hidden. AXLE `verified: null` (1 entry exists today) goes to `warnings[]`, not either bucket.
- **`in_flight`**: derived from `submitted_night.json` / recent `night_submit.log` submission IDs **absent from the ledger** (solver_state.json is stale and is NOT used for this — it only feeds a staleness warning).
- **Name join** (ledger target ↔ `axle_verify.json` keys ↔ `best_proofs/` files): dots→underscores mangling (`A.b.c` ↔ `A_b_c.lean`). Funnel counts `selected_best`/`axle_verified` are **joined-target counts**; raw file counts appear in Health. Orphans on either side (today: ~16 axle entries, ~4 best-proof files matching no target) are counted and listed in `warnings[]`.
- **`registry_attested`**: `registry/theorems.json` covers the whole repo corpus (~11.6k theorems), far larger than this pipeline. The funnel stage counts only **pipeline targets whose dot-name exactly matches a registry entry** — never the raw registry total.
- **Riemann join**: exact dot-name equality against the Riemann Supabase theorem-name column. The implementation plan's first task is confirming table/column with a single query; if no exact-name column exists, the Riemann section ships as `null` + warning — no fuzzy matching.

### Component 2 — Dashboard page (Phase 1: Artifact)

Single-file HTML, all data + JS inline (Artifact CSP: no external requests). Dual light/dark theme, ≥4.5:1 contrast, nothing under 11px, one idea per visual. Sections:

1. **Provenance funnel** (visualization) — horizontal funnel: submissions → unique → candidates → selected → AXLE-verified → registry-attested → Riemann-published. Each stage labeled with its epistemic meaning; banner: *"`PROVED` = Aristotle-internal verdict. Only AXLE-attested counts as verified."*
2. **Yield matrix** (visualization) — domain × tier (campaign) heatmap of verified-rate, with toggle to proved-rate / stopped-rate; row/column totals. This is the steering view: hot domains vs money pits at a glance.
3. **Corpus ledger** (table) — one row per unique target: domain, tiers, stage badge, submissions count, account split, certificate status. Client-side filter (domain/tier/stage/account) + target-name search + column sort. Virtualized/paged rendering (unique targets likely 1–3k rows; page must stay responsive).
4. **Lean certificates** (detail drawer) — clicking a ledger row opens: AXLE result (verified ✓/✗, environment, hash), Lean source preview (monospace, horizontal-scroll container), link to full file on GitHub (repo is public). For unverified candidates: "no independent certificate yet" + its triage priority. **Size budget:** previews inlined only for AXLE-verified targets (~1,014), first ~20 lines each; total single-file HTML target ≤ 2 MB.
5. **Verification triage queue** — the candidates with no AXLE result, ranked (default: tier, then domain verified-rate descending — verify where the domain already proves reliable), with a copy-able list of next-N targets to feed the verify pipeline.
6. **Pipeline health** — recent submission timeline (last 50 events incl. RATE backoffs), admin/chris balance, sync freshness, stale-file and known-bug warnings.
7. **Riemann Lab** — published count + links to riemannlab pages (torus.riemannlab.com / /atlas) when the Supabase join ran; honest empty state otherwise.

### Refresh loop

`python3 aristotle/dashboard_build.py && (Claude session redeploys Artifact)`. Manual for now; optional later: LaunchAgent regenerates `dashboard_data.json` nightly so any Claude session can redeploy in one step. Phase 2 removes the redeploy step entirely.

## Honesty rules (binding)

- Never present `PROVED` counts without the candidate/attested distinction visible in the same view.
- Deduped unique-target counts are the headline; raw submission counts are secondary.
- Missing data (Riemann not queried, stale solver_state) renders as explicit empty/warning states, never fabricated zeros or hidden.
- `verified: false` AXLE results are shown as failures, not filtered out.

## Error handling

- Generator: any missing/corrupt input file → section-level `null` + entry in `warnings[]`; never aborts the whole build over one file.
- Page: renders every section it has data for; `null` sections show the honest empty state.

## Testing

- Generator: pytest with fixture mini-JSONs — dedup correctness, stage assignment (max-stage rule), funnel arithmetic (stages monotonically non-increasing), missing-file degradation.
- Page: eyes-on render in browser before "done" (no headless-only ship), light + dark, 1-row and 0-row filter states.

## Out of scope (Phase 1)

- Write actions (queueing submissions, parking domains) — Phase 2 on ACUTIS.
- Re-running AXLE verification from the page.
- Editing registry or ledger files (generator is strictly read-only).
