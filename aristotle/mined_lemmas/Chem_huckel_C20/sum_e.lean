/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not permit a module docstring `/-! ... -/` before the `import`
line, so the required header appears here as an ordinary block comment.)
-/

import Mathlib

namespace Chem

open Complex Matrix

/-! ### The primitive 20-th root of unity and the associated character -/

/-- The primitive 20-th root of unity `exp (2πi/20)`. -/

lemma sum_e (a : ZMod 20) : ∑ k : ZMod 20, e (a * k) = if a = 0 then 20 else 0 := by
  have hsum : ∑ k : ZMod 20, e (a * k) = ∑ j ∈ Finset.range 20, (e a) ^ j := by
    simp only [e_mul_pow]
    exact Complex.ext rfl rfl
  rw [hsum]
  by_cases ha : a = 0
  · simp [ha, e_zero]
  · rw [if_neg ha, geom_sum_eq (e_ne_one ha), e_pow20]
    simp

