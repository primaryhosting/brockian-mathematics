import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open Filter Topology Set Polynomial

/-- The Sato–Tate density `(2/π) sin²θ` on the interval `[0, π]`. -/

lemma cheb_coeff_top (n : ℕ) : (Chebyshev.U ℝ (n : ℤ)).coeff n = 2 ^ n := by
  have h1 : (Chebyshev.U ℝ (n : ℤ)).natDegree = n := Chebyshev.natDegree_U_natCast ℝ n
  have h := Chebyshev.leadingCoeff_U_natCast ℝ n
  rw [Polynomial.leadingCoeff, h1] at h
  exact h

