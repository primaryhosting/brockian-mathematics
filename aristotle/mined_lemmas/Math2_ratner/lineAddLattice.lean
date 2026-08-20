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

noncomputable def lineAddLattice (v : ℝ × ℝ) : AddSubgroup (ℝ × ℝ) :=
  (LinearMap.toSpanSingleton ℝ (ℝ × ℝ) v).toAddMonoidHom.range
    ⊔ AddSubgroup.closure {((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ))}

/-- **Kronecker's theorem**: if the slope of `v` is irrational then `ℝ v + ℤ²` is dense in `ℝ²`. -/
