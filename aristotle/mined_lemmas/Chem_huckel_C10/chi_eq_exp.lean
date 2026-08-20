import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

open Matrix Polynomial

namespace Chem

/-! ## A primitive tenth root of unity and the associated additive character -/

/-- A primitive `10`-th root of unity. -/

lemma chi_eq_exp (a : ZMod 10) :
    chi a = Complex.exp (((2 * Real.pi * a.val / 10 : ℝ) : ℂ) * Complex.I) := by
  rw [chi_apply, zeta10, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-! ## The Hückel eigenvalues, the Fourier matrix and the adjacency matrix of `C₁₀` -/

/-- The `k`-th Hückel eigenvalue of the cycle `C₁₀`, namely `2 cos (2πk/10)`. -/
