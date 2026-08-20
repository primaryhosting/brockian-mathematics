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

def proj : (ℝ × ℝ) →+ Torus2 :=
  AddMonoidHom.prodMap (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))

/-- The one-parameter unipotent subgroup with direction `v`, acting on `X` by translations:
`t ↦ (t • v mod ℤ²)`. -/
