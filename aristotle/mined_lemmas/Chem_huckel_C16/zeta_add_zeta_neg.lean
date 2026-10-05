/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators Real

namespace Chem

open Complex Finset

/-- A primitive 16-th root of unity. -/

lemma zeta_add_zeta_neg (k : ZMod 16) :
    zeta k + zeta (-k) = 2 * (Real.cos (2 * Real.pi * (k.val : ℝ) / 16) : ℂ) := by
  set θ : ℝ := 2 * Real.pi * (k.val : ℝ) / 16 with hθ
  have hzk : zeta k = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [zeta, w, ← Complex.exp_nat_mul]
    congr 1
    push_cast [hθ]
    ring
  have hzk' : zeta (-k) = Complex.exp (-(θ : ℂ) * Complex.I) := by
    rw [zeta_neg, hzk, ← Complex.exp_neg]
    congr 1; ring
  rw [hzk, hzk', ← Complex.two_cos, Complex.ofReal_cos]

/-- **Hückel theory for `C₁₆`**: the eigenvalues of the adjacency matrix of the cycle
graph `C₁₆` are exactly the numbers `2 cos (2πk/16)` for `k = 0, …, 15`. -/
