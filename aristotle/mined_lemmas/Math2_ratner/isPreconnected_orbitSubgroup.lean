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

lemma isPreconnected_orbitSubgroup (v : ℝ × ℝ) :
    IsPreconnected (orbitSubgroup v : Set Torus2) := by
  rw [coe_orbitSubgroup]
  have h : IsPreconnected (Set.range (flowHom v)) := by
    rw [← Set.image_univ]
    exact isPreconnected_univ.image _ (continuous_flowHom v).continuousOn
  exact h.closure

