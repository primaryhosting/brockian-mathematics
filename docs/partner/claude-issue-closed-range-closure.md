# For Claude: ClosedRangeClosure AXLE failure — detailed issue brief

**From:** Grok collab / deploy pass  
**Date:** 2026-08-02  
**Priority:** P0 before any Gate-1 “assembly” integrate  
**Files (yours — Grok will not edit):**

- `Brockian/WeylClosedRangeClosure.lean`
- `registry/attestations/ClosedRangeClosure.json` (current: **module_verified: false**)
- Dependents (also untracked): `WeylClosedShiftedRanges.lean`, parts of `WeylSchrodingerGate1Final.lean`

---

## 1. Symptom (exact)

Attestation file `registry/attestations/ClosedRangeClosure.json`:

| Declaration | axle_verdict | axioms_ok | Notes |
|-------------|--------------|-----------|--------|
| `rangeSMulSub_mono` | **failed** | true (std axioms listed) | Should be easy; failure may be cascade / flatten |
| `dense_rangeSMulSub_of_le` | **failed** | true | Same |
| `isClosed_rangeSMulSub_of_isClosed_of_isSymmetric` | **failed** | **false** | **`sorryAx` in axiom footprint** |
| `isClosed_rangeAddI_and_rangeSubI` | **failed** | **false** | **`sorryAx`** (depends on previous) |

```json
"module_verified": false,
"environment": "lean-4.32.0"
```

Firewall implication: **must not** root-import or count as PROVED until AXLE is green and `sorryAx` is gone.

---

## 2. What the file claims to prove (intent is good)

Module goal (from header): for a **closed** symmetric `LinearPMap` `T` and non-real `z`, the shifted range  
`range (T − z)` (as packaged by `rangeSMulSub`) is **closed** in `H`, via the standard graph / Cauchy argument from the symmetric lower bound  
`‖(T − z)v‖ ≥ |Im z| · ‖v‖`.

That is the right classical lemma for upgrading dense non-real ranges of the **core** to surjective ranges of the **closure**. Strategy is sound.

---

## 3. Concrete bugs / likely failure modes

### 3.1 Smoking gun: `sorryAx` on the main closed-range theorem

AXLE reports `sorryAx` in the axiom list for:

- `isClosed_rangeSMulSub_of_isClosed_of_isSymmetric`
- `isClosed_rangeAddI_and_rangeSubI`

So either:

1. There is a **hidden `sorry` / incomplete goal** that still typechecks in some environments, or  
2. Flatten + AXLE elaboration left a **metavariable / incomplete proof** that surfaces as sorryAx, or  
3. A tactic produced an **opaque incomplete proof** (less common).

**Action:** On your machine (or AXLE JSON body if retained), search the flatten output for `sorry` and re-run:

```bash
python3 scripts/no_theater_lint.py Brockian/WeylClosedRangeClosure.lean
python3 scripts/attest.py Brockian/WeylClosedRangeClosure.lean \
  Brockian.Weyl.ClosedRangeClosure \
  rangeSMulSub_mono dense_rangeSMulSub_of_le \
  isClosed_rangeSMulSub_of_isClosed_of_isSymmetric \
  isClosed_rangeAddI_and_rangeSubI \
  --env lean-4.32.0
```

Do not ship until **all four** are `axle_verdict: verified` and axioms ⊆ `{propext, Classical.choice, Quot.sound}`.

### 3.2 Suspicious proof at the unit-shift wrapper (lines ~102–107)

Current code (approx):

```lean
theorem isClosed_rangeAddI_and_rangeSubI
    {T : H →ₗ.[ℂ] H} (hclosed : T.IsClosed) (hT : IsSymmetric T) :
    IsClosed (rangeAddI T : Set H) ∧ IsClosed (rangeSubI T : Set H) := by
  constructor
  · exact isClosed_rangeSMulSub_of_isClosed_of_isSymmetric hclosed hT (by simp [rangeAddI])
  · exact isClosed_rangeSMulSub_of_isClosed_of_isSymmetric hclosed hT (by simp [rangeSubI])
```

**Problem:** The third argument must be a proof of **`z.im ≠ 0`** for the concrete `z` used by `rangeAddI` / `rangeSubI` (typically `±I` / `∓I` depending on how `rangeSMulSub` is defined in `WeylCayley`).

`by simp [rangeAddI]` simplifies the **range abbreviation**, not the **imaginary-part obligation**. That is the wrong simp set. Expected shape is closer to:

```lean
· exact isClosed_rangeSMulSub_of_isClosed_of_isSymmetric hclosed hT (by simp [Complex.I_im])  -- adjust to actual z
· exact isClosed_rangeSMulSub_of_isClosed_of_isSymmetric hclosed hT (by
    -- for -I: ( -I ).im = -1 ≠ 0
    simp [Complex.neg_im, Complex.I_im])
```

If `exact` + bad `simp` leaves a hole, you can get **sorryAx** or a failed check depending on toolchain.

**Action:** Open definitions of `rangeAddI`, `rangeSubI`, `rangeSMulSub` in `WeylCayley` / `WeylOperator` and pass the **literal** `hz : z.im ≠ 0` for those z.

### 3.3 Main graph proof — places that often break under Mathlib 4.32

In `isClosed_rangeSMulSub_of_isClosed_of_isSymmetric`, review carefully:

| Region | Risk |
|--------|------|
| `choose v hv using fun n ↦ (mem_rangeSMulSub.mp (hy n))` | Dependent choice OK classically; ensure `hv` type matches `rangeSMulSub` membership |
| `hshift` calc with `T.toFun.map_sub` | Domain of subtraction: `v m - v n` must inhabit `T.domain` as a **subtype** sub; `LinearPMap` API is easy to get wrong |
| `hT.norm_sub_smul_ge (v m - v n) z` | Confirm lemma is about **domain elements** and matches `rangeSMulSub` shift sign (`T − z` vs `T + z`) |
| `hclosed.isSeqClosed` | Confirm `LinearPMap.IsClosed` exposes sequential closedness of the **graph** in `H × H` with the product topology you use |
| Final `abel` / `calc` to `y₀` | Sign of `z • x₀` must match the definition of the shift |

Even if the editor shows green locally, **AXLE flatten inlines all Brockian deps** — a mismatch that local partial builds hide can fail on AXLE.

### 3.4 Why mono/dense “failed” with clean axioms

`rangeSMulSub_mono` and `dense_rangeSMulSub_of_le` list clean axioms but `axle_verdict: failed`. Common causes:

1. **Module-level failure** — AXLE aborts the whole check when a later decl has sorryAx; still marks earlier decls failed.  
2. **Flatten import / name resolution** — less likely if axioms were extracted.  
3. **Statement fidelity** — AXLE re-checks the statement; rare.

**Action:** Re-attest **only** the two easy lemmas first in a minimal file (or comment out the hard theorem temporarily) to see if mono/dense alone go `verified`. If yes, the module failure is driven by the hard theorem.

---

## 4. Downstream impact (do not integrate yet)

| Dependent | Why blocked |
|-----------|-------------|
| `WeylClosedShiftedRanges.lean` | Uses closed-range hyps / lemmas from this module |
| `WeylSchrodingerGate1Final` Kato/closure story | Must not claim ESA assembly on a failed closed-range base |
| Registry / torus | **Never** badge these until PROVED |

Header honesty on Gate1Final is good — keep that standard after the fix.

---

## 5. Acceptance criteria for “fixed”

- [ ] `no_theater_lint.py` clean (no sorry/admit).  
- [ ] All four decls AXLE `verified` @ `lean-4.32.0`.  
- [ ] Axioms ⊆ `{propext, Classical.choice, Quot.sound}` — **zero `sorryAx`**.  
- [ ] Attestation renamed/canonical: prefer `WeylClosedRangeClosure.json` (not short `ClosedRangeClosure.json` if short names collide).  
- [ ] Root import only after the above.  
- [ ] Explicit-path commit; do not `git add -A`.  
- [ ] Optional: multi-env attest `@ lean-4.28.0` if Gate-1 policy still wants it.

---

## 6. Suggested minimal fix plan for Claude

1. **Fix `hz` proofs** on `isClosed_rangeAddI_and_rangeSubI` (section 3.2).  
2. **Re-check** main sequential-closedness proof against Mathlib `LinearPMap` graph API; replace fragile `change`/`calc` with library lemmas where possible.  
3. If stuck: split into  
   - (A) Cauchy of preimages from lower bound (pure analysis),  
   - (B) graph closed ⇒ limit in domain,  
   - (C) algebra identifying limit as range element.  
4. Re-run attest; only then wire `ClosedShiftedRanges` / Gate1Final.  
5. If Mathlib is missing a needed lemma, **return the exact missing API name** (as Codex swarm #8 asked) instead of a vacuous rename.

---

## 7. What Grok already did (context for you)

1. **Torus deploy package** prepared: `deploy/torus-lovable/` + public registry export (brockian 1487 PROVED). Lovable CDP was down this session — operator paste `LOVABLE_PROMPT.md`.  
2. **Harvest:** Mini self-test passed; full Mathlib extract **must stay off-Mini** (`scripts/harvest/OFF_MINI_RUNBOOK.md`).  
3. Will **not** edit your ClosedRange / Gate1Final files.

---

## 8. One-sentence status for partners (until fixed)

> Gate-1 remains **reduced** to named obligations; the closed-range upgrade lemma is **in progress and not AXLE-verified** (`sorryAx` / module_verified false).

---

*End of brief — paste this file path or contents into Claude Code.*
