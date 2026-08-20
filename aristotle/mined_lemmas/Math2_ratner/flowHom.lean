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

noncomputable def flowHom (v : ℝ × ℝ) : ℝ →+ Torus2 :=
  proj.comp (LinearMap.toSpanSingleton ℝ (ℝ × ℝ) v).toAddMonoidHom

/-- The orbit of `x ∈ X` under the unipotent flow in direction `v`. -/
