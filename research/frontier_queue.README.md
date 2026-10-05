# Frontier Target Queue

`research/frontier_queue.json` is the ranked, append-only queue of proof targets.
**Truth lives in this file, in git.** The Supabase table `atlas_frontier_queue` is a
display-only mirror. Spec: `docs/superpowers/specs/2026-08-27-frontier-target-queue-design.md`.

## Schema summary

Top level: `{version, generated_at, generator_commit, entries: [...]}`.

Each entry:

| field | meaning |
|---|---|
| `id` | `ftq-` + sha1(dedup key)[:12]; stable across regenerations |
| `statement` | human-readable statement of the target |
| `lean_target` | `{kind: existing-conjecture\|statement-skeleton\|unformalized, name?, module?, cluster?, wiedijk_index?}` |
| `source` | winning seed source: `wiedijk-gap` · `targets-board` · `registry-conjecture` · `manual` · `frontier_triage` |
| `scores` | `{legibility, tractability, novelty}` 1–5 each; **editorial, not empirical**; merged UPWARD across duplicate sources |
| `rank` | 1-based position by `3·legibility + 2·tractability + novelty`, ties broken by `id` |
| `status` | `open` · `assigned` · `in_progress` · `proved` · `refuted` · `stale` |
| `assigned_engine` | which engine holds it (null when open) |
| `evidence` | `{attestation, links}` — REQUIRED non-empty `attestation` for `proved`/`refuted` |
| `history` | append-only event log `[{at, event, by}]` |

## Legal status transitions

```
open → assigned → in_progress → proved | refuted
```

- **any → `stale`** when every seed source drops the entry — **except `proved`/`refuted`,
  which never go stale**: the generator preserves settled outcomes. (This is a documented
  refinement of the spec's transition table.)
- **`stale` → `open`** when a source re-lists the entry (generator writes a `reopened` event).
- Entries are **never deleted**. Stale, not gone.

## Engine rules

- Engines flip statuses by **editing this file in normal experiment commits**; each flip
  appends a `history` entry whose `by` names the experiment id (e.g. `autolab:exp-…`).
- `proved` and `refuted` REQUIRE `evidence.attestation`. The generator refuses to load a
  queue that violates this (`QueueIntegrityError`).
- **The registry (`registry/theorems.json`) is the only authority on PROVED.** On every
  regeneration the generator reconciles: any entry whose `lean_target.name` is PROVED in
  the registry is flipped to `proved` with the registry name as attestation
  (`by: generator:registry`). An engine's claim without a registry entry is not proof.
- Regeneration preserves `status`, `assigned_engine`, `evidence`, and `history`; it
  refreshes `statement`, `lean_target`, `source`, `scores`, and `rank`.

## Two-repo manual sync

The AutoLab node tree is a separate clone. Registrations landed there (AutoLab main) must be
synced to GitHub manually: workspace pull when `autolab pull` works, else copy from the node
tree (`~/.autolab/ACUTISs-Mac-mini.local/projects/primaryhosting--brockian-mathematics/nodes/…/trees/<tree>/`).
Vendored seed inputs (`research/frontier_triage.json`) came in through that copy path.

## Commands

```bash
# regenerate the queue + review rendering (idempotent; pin --now to diff-check)
python3 scripts/frontier_queue.py --review

# mirror to Riemann Supabase (display only)
python3 scripts/frontier_queue_sync.py --dry-run       # inspect payload, writes nothing
source ~/.openclaw/load-vault.sh
python3 scripts/frontier_queue_sync.py                 # exit 0 synced · 2 BLOCKED (401/no key) · 1 error

# tests
python3 tests/test_frontier_queue.py -v
```

Known blocker: `RIEMANN_SUPABASE_KEY` currently 401s against PostgREST — sync exits 2
(`BLOCKED: service key`) until a real service key is minted. This is loud by design.

## HARD GATE

**No engine consumes this queue until Chris reviews `research/frontier_queue.REVIEW.md`
and says go.** The review rendering is regenerated with `--review`; hand it over after any
material regeneration.
