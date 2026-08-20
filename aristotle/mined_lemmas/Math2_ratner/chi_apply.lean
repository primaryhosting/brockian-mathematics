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

lemma chi_apply (a b : ℤ) (r s : ℝ) :
    chi a b ((r : AddCircle (1 : ℝ)), (s : AddCircle (1 : ℝ)))
      = (((a * r + b * s : ℝ)) : AddCircle (1 : ℝ)) := by
  rw [chi, AddMonoidHom.coprod_apply]
  simp only [zsmulAddGroupHom_apply]
  rw [← AddCircle.coe_zsmul, ← AddCircle.coe_zsmul, ← AddCircle.coe_add]
  norm_num [zsmul_eq_mul]

