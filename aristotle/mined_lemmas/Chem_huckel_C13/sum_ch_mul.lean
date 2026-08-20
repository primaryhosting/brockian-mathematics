/-
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` before any module docstring `/-! ... -/`, so the header
-- above is a plain block comment; it is repeated as the module docstring below.)

import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset

/-- The primitive 13-th root of unity `exp(2πi/13)`. -/

lemma sum_ch_mul (x : ZMod 13) :
    ∑ k : ZMod 13, ch (k * x) = if x = 0 then 13 else 0 := by
  by_cases hx : x = 0
  · subst hx
    simp [ch_zero]
  · rw [if_neg hx]
    have key : ch x * (∑ k : ZMod 13, ch (k * x)) = ∑ k : ZMod 13, ch (k * x) := by
      rw [Finset.mul_sum]
      have hstep : ∀ k : ZMod 13, ch x * ch (k * x) = ch ((k + 1) * x) := by
        intro k
        rw [show (k + 1) * x = k * x + x by ring, ch_add, mul_comm]
      simp_rw [hstep]
      exact Equiv.sum_comp (Equiv.addRight (1 : ZMod 13)) (fun k => ch (k * x))
    have hzero : (ch x - 1) * (∑ k : ZMod 13, ch (k * x)) = 0 := by
      linear_combination key
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd (by linear_combination h : ch x = 1) (ch_ne_one hx)
    · exact h

/-- The Hückel (adjacency) eigenvalues of `C₁₃`. -/
