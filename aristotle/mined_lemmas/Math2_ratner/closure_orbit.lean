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

lemma closure_orbit (v : ℝ × ℝ) (x : Torus2) :
    closure (orbit v x) = (fun y => x + y) '' (orbitSubgroup v : Set Torus2) := by
  rw [orbit_eq, coe_orbitSubgroup]
  exact ((Homeomorph.addLeft x).image_closure _).symm

