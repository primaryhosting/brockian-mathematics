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

lemma flowHom_apply_coe (v : ℝ × ℝ) (t : ℝ) :
    flowHom v t = (((t * v.1 : ℝ) : AddCircle (1 : ℝ)), ((t * v.2 : ℝ) : AddCircle (1 : ℝ))) := by
  simp [flowHom, proj, LinearMap.toSpanSingleton, Prod.smul_def, smul_eq_mul]

