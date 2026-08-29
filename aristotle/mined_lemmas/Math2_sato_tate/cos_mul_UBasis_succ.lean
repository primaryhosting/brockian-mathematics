/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Real MeasureTheory
open scoped Topology BigOperators Classical

namespace Math2

/-! ## The Sato–Tate distribution -/

/-- The Sato–Tate density `(2/π) sin²θ` on `[0, π]`. -/

lemma cos_mul_UBasis_succ (j : ℕ) (x : ℝ) :
    Real.cos x * UBasis (j + 1) x = (UBasis (j + 2) x + UBasis j x) / 2 := by
  have h := Polynomial.Chebyshev.U_add_two (R := ℝ) (n := (j : ℤ))
  have h' : (Polynomial.Chebyshev.U ℝ ((j : ℤ) + 2)).eval (Real.cos x)
      = 2 * Real.cos x * (Polynomial.Chebyshev.U ℝ ((j : ℤ) + 1)).eval (Real.cos x)
        - (Polynomial.Chebyshev.U ℝ (j : ℤ)).eval (Real.cos x) := by
    rw [h]
    simp
  have e1 : (((j + 2 : ℕ)) : ℤ) = (j : ℤ) + 2 := by push_cast; ring
  have e2 : (((j + 1 : ℕ)) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
  simp only [UBasis, e1, e2]
  rw [h']
  ring

