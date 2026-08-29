/-
  CompactCriterion.lean — an abstract compactness criterion: an operator whose
  unit-ball image is uniformly approximable by finite-dimensional subspaces is
  a compact operator.
-/
import Mathlib

open Metric Filter

namespace Brockian.Weyl.OscillatorCompact

/-- An operator whose closed-unit-ball image is uniformly approximable by
finite-dimensional subspaces is a compact operator. -/

theorem smulPMap_isSymmetric (c : ℝ) : IsSymmetric (smulPMap (H := H) c) := by
  intro x y
  rw [smulPMap_apply, smulPMap_apply, inner_smul_left, inner_smul_right]
  simp

end Brockian.Weyl.Operator

/-! ## Brockian/WeylSchrodingerMinimal.lean (reconstruction)

The minimal `L²(ℝ)` scaffolding: the Hilbert space, the Schwartz core embedding,
the second-derivative operator on the Schwartz space and the symmetry of the
kinetic term (integration by parts). -/

namespace Brockian.Weyl.SchrodingerMinimal

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace

/-- The Hilbert space `L²(ℝ, ℂ)`. -/
noncomputable abbrev H2 := Lp ℂ 2 (volume : Measure ℝ)

/-- The Schwartz core of `L²(ℝ)`. -/
