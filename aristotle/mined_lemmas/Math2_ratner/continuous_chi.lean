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

lemma continuous_chi (a b : ℤ) : Continuous (chi a b) := by
  have h : (⇑(chi a b)) = fun p : Torus2 => a • p.1 + b • p.2 := by
    ext p; simp [chi, zsmulAddGroupHom]
  rw [h]
  exact ((continuous_zsmul a).comp continuous_fst).add ((continuous_zsmul b).comp continuous_snd)

