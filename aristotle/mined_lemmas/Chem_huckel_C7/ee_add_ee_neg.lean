import Mathlib
/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Chem

open Complex Finset Matrix

/-- A primitive 7-th root of unity. -/

lemma ee_add_ee_neg (k : Fin 7) : ee k + ee (-k) = (lam k : ℂ) := by
  have hz : ee k = Complex.exp (((2 * Real.pi * k.val / 7 : ℝ) : ℂ) * Complex.I) := by
    simp only [ee, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h : ee k * ee (-k) = 1 := by rw [← ee_add]; simp [ee_zero]
  have hinv : ee (-k) = (ee k)⁻¹ := (DivisionMonoid.inv_eq_of_mul _ _ h).symm
  rw [hinv, hz, ← Complex.exp_neg, lam]
  rw [Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

/-- The adjacency matrix of the cycle graph `C₇` acts on a vector by summing over the two
neighbours of each vertex. -/
