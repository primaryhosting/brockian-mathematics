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

lemma chi_add_chi_neg (k : ZMod 10) : chi k + chi (-k) = huckelEigenvalue k := by
  set θ : ℝ := 2 * Real.pi * k.val / 10 with hθ
  have hc : chi k = Complex.exp ((θ : ℂ) * Complex.I) := chi_eq_exp _
  have hne : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have h1 : chi (-k) * Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
    rw [← hc, ← AddChar.map_add_eq_mul]; simp
  have h2 : chi (-k) = Complex.exp (-(θ : ℂ) * Complex.I) := by
    rw [(mul_eq_one_iff_eq_inv₀ hne).mp h1, ← Complex.exp_neg]
    ring_nf
  rw [hc, h2, huckelEigenvalue, ← hθ, Complex.ofReal_mul, Complex.ofReal_cos]
  push_cast
  exact (Complex.two_cos _).symm

/-! ## The Fourier matrix diagonalises the adjacency matrix -/

