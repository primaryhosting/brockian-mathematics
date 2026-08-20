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

lemma dense_image_proj {A : Set (ℝ × ℝ)} (hA : Dense A) : Dense (proj '' A) := by
  rw [dense_iff_inter_open]
  intro U hU hne
  obtain ⟨y, hyU⟩ := hne
  obtain ⟨p, rfl⟩ := surjective_proj y
  obtain ⟨q, hq1, hq2⟩ :=
    dense_iff_inter_open.1 hA (proj ⁻¹' U) (hU.preimage continuous_proj) ⟨p, hyU⟩
  exact ⟨proj q, hq1, ⟨q, hq2, rfl⟩⟩

