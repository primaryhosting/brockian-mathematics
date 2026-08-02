# Multi-Agent Collaboration Protocol — Claude × Codex × Grok

**Updated:** 2026-08-02 (Grok collab pass)  
**Shared repo:** `brockian-mathematics` on `main` (prefer worktrees/branches when possible)  
**SSOT for claims:** `docs/AGENT-COORDINATION.md` (append-only Active Claims)

---

## 1. How we collaborate (not compete)

| Agent | Primary strength | Default lanes |
|-------|------------------|---------------|
| **Claude** | Statement design, Gate-1 analysis packaging, long classical proofs | Weyl/Schrodinger/weak-reg modules; Harmonic/Aristotle monitoring |
| **Codex** | Weyl conditional attack, scaffolding, tooling hygiene | Weak regularity, Kato–Rellich, Plancherel interfaces; registry hygiene |
| **Grok** | Finite algebra, sieve, packaging, partner/pipeline, reduce-only frontier | Admissibility/Goldbach local, distillation/refute, partner docs, settle bridge |
| **Aristotle/Harmonic** | Hard classical closes | `aristotle/*` race targets only |

**Rule:** One owner per file path. Append a claim line before writing. Never `git add -A`.

---

## 2. LIVE status (2026-08-02 afternoon)

### Claude / Codex Gate-1 package — **SHIPPED** ✅

**Commit:** `d20fd09` — `feat(weyl): add weak primitive and Kato resolvent reductions`  
**Registry tip (after their ship):** ~**1487 PROVED** / 309 DEFINITION / 21 CONDITIONAL

| File | Status | Notes |
|------|--------|-------|
| `Brockian/WeylWeakPrimitiveLocal.lean` | **in registry** | Hypothesis-discharge of `WeakToPrimitiveRegularity` — **stretch (drop H) still open** |
| `Brockian/WeylKatoResolventConstruction.lean` | **in registry** | Unit-shift resolvent **interface** — **construction from free-Δ still open** |
| Attestations + root import | done on `d20fd09` | Grok does not re-commit |

**Honesty for partners:** these packages **reduce** Gate-1; they do **not** close unbounded ESA or full 1D elliptic regularity.

**Remaining Claude/Codex dirty (optional):** `aristotle/kato-bounded/KatoBounded.lean` (sorry closed?), `aristotle/franklin/`, `aristotle/weak-regularity/` — owner-only.

### Grok (this pass) — complementary only

| Owned | Action |
|-------|--------|
| `docs/MULTI-AGENT-COLLAB.md` | this protocol |
| `docs/AGENT-COORDINATION.md` LIVE board | status + claims |
| `pipeline/*` | cards link to Claude/Codex modules; ledger refresh |
| `scripts/agent_board.py` | shared status snapshot |
| Partner pack `docs/partner/*` | already on `7489f9e` |
| Finite / sieve / refute / distill | SAIR + CS lane |

**Grok will NOT edit:** any `Weyl*`, `aristotle/kato*`, Claude/Codex dirty registry paths mid-integrate.

### Avoid (shared traps)

- `aristotle/franklin/target.lean` and `aristotle/weak-regularity/target.lean` may be **wrong paste** — owner should rewrite or delete; others leave alone.
- Duplicate attestation short names — keep `Weyl*` canonical stems.
- RH / global Goldbach — reduce-only schemas; never PROVED.

---

## 3. Handoff messages

### To Claude

**Thank you — package landed on `d20fd09`.** Grok recognized the ship in the pipeline ledger and PROGRAM-REPORT (1487 PROVED). Stretch for a later swarm: (1) prove `DistributionalPrimitiveHypothesis` for continuous bounded \(V\); (2) free-Δ Plancherel / Harmonic race. Optional: clean `aristotle/franklin|weak-regularity` targets if still wrong-paste.

### To Codex

**Thank you — Gate-1 reductions are registry-backed.** Next high-value Weyl lane remains A1 weak regularity (or Aristotle pull) and constructing resolvents from free-Laplacian inputs (not re-packaging the interface). Do not reopen Franklin (DISCHARGED). Leave Grok `pipeline/` and partner docs alone.

### To Grok (self)

Pipeline cards + PROGRAM-REPORT refreshed against `d20fd09`. Stay on SAIR refute, torus honesty (Lovable), Mathlib/PhysLean harvest — reduce-only on RH/Goldbach.

---

## 4. Suggested next splits (no collision)

| Priority | Owner | Target |
|----------|-------|--------|
| P0 | Claude/Codex | Commit Gate-1 package on main |
| P1 | Codex | A1 weak regularity (or Aristotle pull `c400008b`) |
| P1 | Claude | A3 free-Δ Plancherel stretch / Harmonic race |
| P1 | Grok | SAIR Stage-2 refute loop + sieve certs + torus honesty punch-list (Lovable) |
| P2 | Grok | Mathlib/PhysLean harvest inventory execution (import plan only until pin agreed) |
| P2 | Any | Dual-prover on next PROVED candidates |

---

## 5. Shared commands

```bash
# Who is dirty / what registry says
python3 scripts/agent_board.py

# Certificate path (all agents)
python3 scripts/pipeline_attest_bridge.py Brockian/Foo.lean Decl1 Decl2
python3 scripts/settle.py Brockian/Foo.lean --env lean-4.32.0
python3 scripts/refute.py --A "x*x = x" --B "x*y = y*x"

# Partner surface
python3 scripts/gen_program_report.py
python3 -m pipeline.scripts.pipeline_cli ledger
```

---

## 6. Conflict resolution

1. If two agents claim the same file → **first claim line in AGENT-COORDINATION wins**; second picks a new file.
2. If mid-integrate dirty files exist → **non-owners do not commit or reformat them**.
3. If dual-prover disagree → `BLOCKED`, human triage (settle factory rule).
4. Prefer **worktrees** (`git worktree add ../brockian-claude gate1-claude`) for multi-hour Gate-1 work.

---

*Grok collab pass: documentation + board only; Gate-1 proof files left to Claude/Codex.*
