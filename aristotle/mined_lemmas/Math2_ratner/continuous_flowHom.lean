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

lemma continuous_flowHom (v : ℝ × ℝ) : Continuous (flowHom v) := by
  have h : (⇑(flowHom v)) = fun t : ℝ => proj (t • v) := rfl
  rw [h]
  exact continuous_proj.comp (continuous_id.smul continuous_const)

