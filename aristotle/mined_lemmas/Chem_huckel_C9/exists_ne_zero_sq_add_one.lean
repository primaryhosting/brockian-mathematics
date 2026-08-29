import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open SimpleGraph Matrix

namespace Chem

/-- The primitive 9-th root of unity `exp (2πi/9)`. -/

lemma exists_ne_zero_sq_add_one (μ : ℂ) : ∃ z : ℂ, z ≠ 0 ∧ z ^ 2 + 1 = μ * z := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (n := 2) (μ ^ 2 - 4) (by norm_num)
  have key : ((μ + s) / 2) ^ 2 + 1 = μ * ((μ + s) / 2) := by field_simp; linear_combination hs
  refine ⟨(μ + s) / 2, ?_, key⟩
  intro h
  rw [h] at key
  simp at key

/-- Every eigenvalue of `C₉` comes from a 9-th root of unity. -/
