/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The adjacency (Hückel) matrix of the cycle graph `C₁₄` is diagonalised by the discrete Fourier
transform on `ZMod 14`; its characteristic polynomial is therefore
`∏_{k=0}^{13} (X - 2 cos (2πk/14))`, i.e. its eigenvalues are `2 cos (2πk/14)` for `k = 0, …, 13`.
-/

open Complex Polynomial Matrix

namespace Chem

noncomputable section

/-- A primitive 14-th root of unity. -/

theorem chi_sum (a : ZMod 14) : ∑ k : ZMod 14, chi (a * k) = if a = 0 then 14 else 0 := by
  by_cases ha : a = 0
  · subst ha; simp [ZMod.card]
  · rw [if_neg ha]
    simpa [AddChar.mulShift_apply] using AddChar.sum_eq_zero_of_ne_one (chi_isPrimitive ha)

