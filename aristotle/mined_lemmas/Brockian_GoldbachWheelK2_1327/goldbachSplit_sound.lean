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

theorem goldbachSplit_sound {m : ℕ} (hm : m ≤ 2703) (h : goldbachSplit m = true) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ m = p + q := by
  rw [goldbachSplit, List.any_eq_true] at h
  obtain ⟨p, _, hp⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨hpp, hplt⟩, hqp⟩ := hp
  refine ⟨p, m - p, isPrimeB_sound (by omega) hpp, isPrimeB_sound (by omega) hqp, by omega⟩

/-- The exhaustive wheel check: every even number `2n` with `2 ≤ n ≤ 1327` splits. -/
