/-
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-! ## A clocked model of computation

Programs are natural numbers (their own Gödel numbers).  A code `c` is decoded
on the fly:

* `0` : the constant `0`
* `1` : the successor function
* `2` : first projection of the Cantor pairing
* `3` : second projection of the Cantor pairing
* `4` : the *clocked universal machine*: on input `⟪c', y, k⟫` it simulates the
  program `c'` on input `y` for `k` steps and outputs the result (or `0` if
  the simulation did not finish);  this costs `k + 1` steps
* `5` : the boolean complement `x ↦ if x = 0 then 1 else 0`
* `6` : the identity
* `7 + 4 * ⟪i, j⟫ + 0` : pairing of the results of `i` and `j`
* `7 + 4 * ⟪i, j⟫ + 1` : composition `i ∘ j`
* `7 + 4 * ⟪i, j⟫ + 2` : primitive recursion
* `7 + 4 * ⟪i, j⟫ + 3` : unbounded search (`rfind`)

`eval s c x` runs the program `c` on input `x` with a budget of `s` steps and
returns `none` if the budget is exhausted.  Every constructor consumes one unit
of the budget, so `eval` is a genuine (if coarse) cost model. -/

theorem eval_mono_succ : ∀ s c x v, eval s c x = some v → eval (s+1) c x = some v := by
  intro s
  induction s with
  | zero => intro c x v h; simp at h
  | succ s ih =>
    intro c x v h
    rcases code_cases c with hc | ⟨i, j, hc⟩
    · interval_cases c
      · simpa using h
      · simpa using h
      · simpa using h
      · simpa using h
      · rw [show (4:ℕ) = cUniv from rfl, eval_cUniv_def] at h ⊢
        by_cases hk : (Nat.unpair (Nat.unpair x).2).2 ≤ s
        · rw [if_pos hk] at h
          rw [if_pos (by omega)]
          exact h
        · rw [if_neg hk] at h
          exact absurd h (by simp)
      · rw [show (5:ℕ) = cNot from rfl] at h ⊢
        simpa using h
      · rw [show (6:ℕ) = cId from rfl] at h ⊢
        simpa using h
    · rcases hc with hc | hc | hc | hc <;> subst hc
      · rw [eval_cPair] at h ⊢
        simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
        obtain ⟨a, ha, b, hb, hab⟩ := h
        exact ⟨a, ih _ _ _ ha, b, ih _ _ _ hb, hab⟩
      · rw [eval_cComp] at h ⊢
        simp only [Option.bind_eq_some_iff] at h ⊢
        obtain ⟨b, hb, hv⟩ := h
        exact ⟨b, ih _ _ _ hb, ih _ _ _ hv⟩
      · rcases hx : (Nat.unpair x).2 with _ | n
        · rw [eval_cPrec_zero _ _ _ _ hx] at h ⊢
          exact ih _ _ _ h
        · rw [eval_cPrec_succ _ _ _ _ _ hx] at h ⊢
          simp only [Option.bind_eq_some_iff] at h ⊢
          obtain ⟨b, hb, hv⟩ := h
          exact ⟨b, ih _ _ _ hb, ih _ _ _ hv⟩
      · rw [eval_cRfind] at h ⊢
        simp only [Option.bind_eq_some_iff] at h ⊢
        obtain ⟨b, hb, hv⟩ := h
        refine ⟨b, ih _ _ _ hb, ?_⟩
        split_ifs at hv ⊢ with hb0
        · exact hv
        · exact ih _ _ _ hv

