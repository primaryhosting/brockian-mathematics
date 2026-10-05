/-
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Brockian

/-- `noDiv n k` is `true` when no `d` with `2 ≤ d ≤ k` divides `n`. -/

theorem noDiv_spec (n : ℕ) :
    ∀ k : ℕ, noDiv n k = true → ∀ d : ℕ, 2 ≤ d → d ≤ k → ¬ d ∣ n := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => intro _ d hd hdk; omega
    | 1 => intro _ d hd hdk; omega
    | (j + 2) =>
      intro h d hd hdk
      simp only [noDiv, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      rcases Nat.lt_or_ge d (j + 2) with hlt | hge
      · exact ih (j + 1) (by omega) h.2 d hd (by omega)
      · have hdj : d = j + 2 := by omega
        subst hdj
        rw [Nat.dvd_iff_mod_eq_zero]
        exact h.1

/-- Soundness of the trial–division test in the range we use it in. -/
