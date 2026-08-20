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

lemma orbit_eq (v : ℝ × ℝ) (x : Torus2) :
    orbit v x = (fun y => x + y) '' (Set.range (flowHom v)) := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩; exact ⟨flowHom v t, ⟨t, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨t, rfl⟩, rfl⟩; exact ⟨t, rfl⟩

