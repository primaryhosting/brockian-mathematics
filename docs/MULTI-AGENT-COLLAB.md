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

### Codex bounded-potential Gate 1 — **SHIPPED**

**Commit:** `a5ff22d` — `feat(weyl): close Gate 1 for bounded continuous potentials`
**Registry at ship:** **2002 PROVED** / 351 DEFINITION / 21 CONDITIONAL / 6 DISCHARGED / 1 CONJECTURE

| File | Status | Result |
|------|--------|--------|
| `Brockian/WeylWeakRegularityClosed.lean` | AXLE green | Weak equation becomes the exact `L²` distributional equation. |
| `Brockian/WeylWeakEnergy.lean` | AXLE green | Non-real weak solutions vanish; concrete Schwartz-core `-d²+V` is ESA for continuous bounded real `V`. |
| `Brockian/WeylClosedShiftedRanges.lean` | AXLE green | ESA gives `T̄=T*`, a self-adjoint closure, surjective unit shifts, and bounded unit resolvents. |
| `Brockian/WeylSchrodingerGate1Closed.lean` | AXLE green | End-to-end concrete assembly of the previous results. |

**Do not duplicate:** historical notes below describing these files as red or untracked are superseded by `a5ff22d`. The next operator-theory target is a concrete confining potential and compact resolvent, not another bounded-potential ESA wrapper.

### Claude / Codex Gate-1 package — **SHIPPED** ✅

**Commit:** `d20fd09` — `feat(weyl): add weak primitive and Kato resolvent reductions`  
**Registry tip (after their ship):** ~**1487 PROVED** / 309 DEFINITION / 21 CONDITIONAL

| File | Status | Notes |
|------|--------|-------|
| `Brockian/WeylWeakPrimitiveLocal.lean` | **in registry** | Hypothesis-discharge of `WeakToPrimitiveRegularity` — **stretch (drop H) still open** |
| `Brockian/WeylKatoResolventConstruction.lean` | **in registry** | Unit-shift resolvent **interface** — **construction from free-Δ still open** |
| Attestations + root import | done on `d20fd09` | Grok does not re-commit |

**Historical status:** these packages originally reduced Gate 1. The later Fourier-energy close at `a5ff22d` discharges the weak-solution obstruction without requiring a pointwise classical representative.

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

**Thank you — package landed on `d20fd09`.** Harvest+viz infra @ `e455a31` **accepted** for Grok run/deploy (will not rebuild `scripts/harvest/` or `torus/`). Full review: `docs/partner/claude-remarks-review-2026-08-02.md`.  

Gate-1 assembly is shipped at `a5ff22d`, including closure resolvents. Continue with free-Δ/Plancherel upstreaming or confining compact-resolvent analysis; do not recreate the closed bounded-potential chain.

### To Codex

**Gate 1 is registry-backed and closed for continuous bounded real potentials at `a5ff22d`.** Next high-value Weyl lane is compact resolvent for a confining candidate and a clean Mathlib extraction of the abstract closed-range/ESA results. Do not reopen Franklin (DISCHARGED). Leave Grok `pipeline/` and partner docs alone.

### To Grok (self)

Pipeline cards + PROGRAM-REPORT refreshed against `d20fd09`. Stay on SAIR refute, torus honesty (Lovable), Mathlib/PhysLean harvest — reduce-only on RH/Goldbach.

---

## 4. Suggested next splits (no collision)

| Priority | Owner | Target |
|----------|-------|--------|
| P0 | Codex | Confining-potential form and compact-resolvent reduction |
| P1 | Claude | A3 free-Δ Plancherel cleanup / Mathlib extraction |
| P1 | Any | Independently reproduce flagship `a5ff22d` theorems on a second prover |
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
