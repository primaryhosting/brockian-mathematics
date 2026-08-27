# Frontier Target Queue — Design

**Date:** 2026-08-27
**Status:** Approved design (Workstream A of the hyper-leverage program: A queue → B miner → C papers → D Mathlib PR)
**Home:** `research/frontier_queue.json` in `primaryhosting/brockian-mathematics` (truth) + `atlas_frontier_queue` in Riemann Supabase (mirror)

## 1. Purpose

One ranked, provenance-carrying queue of proof targets, so every proving engine —
the Brockian AutoLab wave loop, the builder-prover's 30-minute cycles, Aristotle
night submissions — attacks the *same, best* targets instead of self-picking
registry gaps. Leverage is measured in externally-verifiable wins; the queue is
where "what should we prove next" becomes a ranked, reviewable artifact. It later
becomes the live back end of the Formal Atlas frontier view
(`2026-08-26-formal-atlas-design.md`).

## 2. Goals / Non-goals

**Goals**
- Single source of truth for open proof targets, versioned in git, append-only.
- Deterministic v1 ranking from existing signals; human-reviewable before any
  engine consumes it.
- Live mirror in Riemann Supabase for the site/Atlas to read.
- Status lifecycle that engines can drive (via normal git commits on their
  branches) without ever becoming an authority on mathematical truth.

**Non-goals**
- The queue never claims PROVED — `registry/theorems.json` (and its sanitized
  public export) remains the only authority; a queue entry's `proved` status is
  a *pointer* to an attestation, not a claim.
- No LLM scoring in v1 (arrives as the Miner workstream, which is just a fifth
  source feeding the same schema).
- No AutoLab objective rewrite in this workstream (explicitly gated on the
  user's review of the first generated queue).
- No UI beyond the raw Supabase table.

## 3. The queue file

`research/frontier_queue.json`:

```json
{
  "version": 1,
  "generated_at": "<ISO>",
  "generator_commit": "<sha>",
  "entries": [
    {
      "id": "ftq-<stable-hash>",
      "statement": "<informal, one sentence>",
      "lean_target": {
        "kind": "existing-conjecture | statement-skeleton | unformalized",
        "name": "<registry name, when it exists>",
        "module": "<module, when it exists>",
        "skeleton": "<proposed Lean statement, when kind=statement-skeleton>"
      },
      "source": "frontier_triage | registry-conjecture | targets-board | wiedijk-gap | miner | manual",
      "scores": { "legibility": 0-5, "tractability": 0-5, "novelty": 0-5 },
      "rank": 1,
      "status": "open | assigned | in_progress | proved | refuted | stale",
      "assigned_engine": "autolab-brockian | builder-prover | aristotle-night | null",
      "evidence": { "attestation": "<AXLE ref / registry name>", "links": [] },
      "history": [ { "at": "<ISO>", "event": "<what>", "by": "<who/which engine>" } ]
    }
  ]
}
```

Rules:
- `id` is a stable hash of the normalized statement — regeneration must not
  re-mint ids (dedup key across sources and across runs).
- `history` is append-only; entries are never deleted. Targets that fall out of
  every source flip to `stale`, they don't vanish.
- `proved` and `refuted` require `evidence.attestation`; the generator validates
  this invariant and refuses to emit a file that violates it.
- Regeneration merges *onto* the previous queue file: statuses and history are
  preserved; only ranks/scores/new entries change.

## 4. Generator — `scripts/frontier_queue.py`

Stdlib-only Python (the repo's script conventions), run manually for v1
(`python3 scripts/frontier_queue.py`), cron later.

**Seed sources (v1):**
1. `research/frontier_triage.json` — the AutoLab agent's ranked 60 conjectures
   with GO/NO-GO recommendations (merged to the AutoLab project main; synced
   into this repo as part of this workstream).
2. Registry conjectures — the 40 `register: CONJECTURE` entries in
   `registry/theorems.json` (+ 20 CONDITIONAL as lower-priority variants).
3. Targets board — the top-100 problems dataset behind `/targets`
   (25 statement-formalized entries rank highest; the "our formalization
   frontier" list next).
4. Wiedijk-gaps — entries of the "Formalizing 100 Theorems" list with no
   counterpart in the corpus (statement-level: `kind: unformalized`).

**Ranking (v1, deterministic):**
`rank_score = 3·legibility + 2·tractability + 1·novelty`, where
- legibility: source-weighted (wiedijk-gap 5, targets-board 4, named registry
  conjectures 3, triage-internal 2);
- tractability: triage GO=5 / triage listed=3 / statement-formalized=3 /
  unformalized=1;
- novelty: 3 baseline, 5 for entries no other library has (per Atlas data once
  it exists; constant in v1 and documented as such).
Ties break alphabetically by id (stable output; diffs stay reviewable).
Weights live as constants at the top of the script with a comment that they are
editorial, not empirical.

## 5. Supabase mirror

- Table `atlas_frontier_queue` (Riemann Supabase): columns mirror the entry
  schema (jsonb for `lean_target`/`scores`/`evidence`/`history`) + `synced_at`.
- `scripts/frontier_queue_sync.py`: full upsert of the current file, delete
  nothing; RLS = SELECT to anon, writes via service key only.
- ⚠ **Known blocker:** the existing `RIEMANN_SUPABASE_KEY` 401s as a service
  key (same blocker as the fleet panel). The table DDL + sync script ship
  regardless; if the key still 401s at build time, the sync exits with a loud
  `BLOCKED: service key` message and the spec's acceptance simply records the
  mirror as pending-key. Minting the key is a human (Chris) action.

## 6. Consumers & lifecycle

1. **Human review (gate).** The first generated queue goes to Chris as a ranked
   table. Nothing consumes the queue before his go.
2. **Brockian AutoLab loop (after the gate).** The project's optimization
   prompt is updated (separate, small change — not part of this build) so waves
   (a) pick the highest-ranked `open` entries, (b) flip `open → assigned →
   in_progress → proved/refuted` by editing the queue file in their normal
   experiment commits, with history entries naming the experiment id. Merged
   experiments carry the status change back to project main; the repo-sync step
   (below) carries it to GitHub.
3. **Builder-prover / Aristotle night-submit (later).** Both already read this
   repo; wiring them to the queue is a follow-up outside this workstream.

**Repo-sync note (explicit, because two repos exist):** the AutoLab project
repo is a *copy* of the GitHub repo. Queue updates made by AutoLab experiments
land on AutoLab main; a small `just`-style pull step (documented in the queue
README) brings them back to GitHub. v1 keeps this manual — same posture as the
stranded Zumkeller theorems, which this workstream also syncs back.

## 7. Testing

- Generator unit tests (stdlib `unittest`, matching repo conventions):
  stable-id dedup across sources; status/history preservation across regen;
  proved-requires-attestation invariant; deterministic ordering.
- A golden-file test with a small fixture of each source proving the merged
  output byte-stable.
- Sync script: dry-run mode asserting the upsert payload against the file;
  401-path prints `BLOCKED` and exits nonzero without partial writes.

## 8. Deliverables (v1)

1. `research/frontier_queue.json` — first generated queue from the 4 seed
   sources (plus the triage file synced into the repo).
2. `scripts/frontier_queue.py` + tests.
3. `atlas_frontier_queue` DDL migration + `scripts/frontier_queue_sync.py`
   (live if the service key works; loud-blocked otherwise).
4. `research/frontier_queue.README.md` — schema, lifecycle, engine rules,
   repo-sync step.
5. Zumkeller sync-back: the 4 AXLE-verified theorems from AutoLab main
   registered into the GitHub repo's corpus via the normal registry path.
6. A ranked human-readable rendering of queue v1 for Chris's review gate.

## 9. Risks

- **Two-repo drift** (GitHub vs AutoLab copy): mitigated by the documented
  manual sync step and append-only merges; accepted for v1.
- **Score theater:** deterministic weights are editorial. Mitigated by labeling
  them as such in-file and gating engine consumption on human review.
- **Service-key blocker** stalls the mirror, not the queue: truth is the repo
  file; the site simply waits.
- **Engine status-flips without proof:** prevented structurally — `proved`
  without attestation fails generator validation and CI.
