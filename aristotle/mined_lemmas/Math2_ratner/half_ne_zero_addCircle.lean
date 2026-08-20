import Mathlib

/-!
# Ratner
Category: Frontier Math
Target: Math2.ratner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math2

/-- The homogeneous space `X = G / Γ` for `G = ℝ²` and the lattice `Γ = ℤ²`, i.e. the
two-dimensional torus. -/
abbrev Torus2 : Type := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

/-- The projection `G = ℝ² → X = ℝ²/ℤ²`. -/

lemma half_ne_zero_addCircle : (((1 : ℝ) / 2 : ℝ) : AddCircle (1 : ℝ)) ≠ 0 := by
  intro hzero
  rw [AddCircle.coe_eq_zero_iff] at hzero
  obtain ⟨n, hn⟩ := hzero
  simp [zsmul_eq_mul] at hn
  have h2 : ((2 * n : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by push_cast; linarith
  have := Int.cast_injective (α := ℝ) h2
  omega

/-- Conversely, a nontrivial integral relation gives a proper subtorus containing the orbit. -/
