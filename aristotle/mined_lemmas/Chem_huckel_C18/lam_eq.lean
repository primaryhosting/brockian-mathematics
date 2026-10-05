/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Hückel model for the annulene `C₁₈` uses the adjacency matrix of the cycle
graph `C₁₈`.  We show that its eigenvalues are exactly the `18` numbers
`2 cos (2πk/18)`, `k = 0, …, 17`.
-/

namespace Chem

open Complex Matrix

/-- The adjacency matrix of the cycle graph `C₁₈` on the vertex set `Fin 18`:
vertices `i` and `j` are adjacent iff they are consecutive modulo `18`. -/

lemma lam_eq (k : ℕ) :
    ((2 * Real.cos (2 * Real.pi * k / 18) : ℝ) : ℂ) = zeta ^ k + (zeta ^ k) ^ 17 := by
  have h18 : (zeta ^ k) ^ 18 = 1 := zeta_pow_pow_eighteen k
  have hne : zeta ^ k ≠ 0 := by
    intro h
    rw [h] at h18
    simp at h18
  have h17 : (zeta ^ k) ^ 17 = (zeta ^ k)⁻¹ := by
    field_simp
    linear_combination h18
  rw [h17, zeta_pow k, ← Complex.exp_neg]
  rw [Complex.exp_mul_I,
    show -((2 * Real.pi * k / 18 : ℝ) * I) = (-(2 * Real.pi * k / 18 : ℝ)) * I by ring,
    Complex.exp_mul_I]
  push_cast
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

/-- The fundamental computation: the geometric vector `j ↦ z ^ j` is an eigenvector of the
cycle adjacency matrix whenever `z ^ 18 = 1`. -/
