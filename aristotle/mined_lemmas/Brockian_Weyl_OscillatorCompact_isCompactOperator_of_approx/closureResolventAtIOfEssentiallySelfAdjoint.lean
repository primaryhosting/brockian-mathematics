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

noncomputable def closureResolventAtIOfEssentiallySelfAdjoint {T : H →ₗ.[ℂ] H}
    (hsym : IsSymmetric T) (hd : Dense (T.domain : Set H))
    (hESA : EssentiallySelfAdjoint T) : ResolventAtI T.closure := by
  have hsymc := isSymmetric_closure hsym hd
  have hzadd : |(-Complex.I).im| = 1 := by simp
  have hzsub : |(Complex.I).im| = 1 := by simp
  have hdefadd : deficiencySpace T ((starRingEnd ℂ) (-Complex.I)) = ⊥ := by
    simpa using hESA.1
  have hdefsub : deficiencySpace T ((starRingEnd ℂ) (Complex.I)) = ⊥ := by
    simpa using hESA.2
  exact
    { Radd := shiftedInverse T.closure (-Complex.I) hsymc hzadd
        (exists_shifted_eq hsym hd hzadd hdefadd)
      Rsub := shiftedInverse T.closure Complex.I hsymc hzsub
        (exists_shifted_eq hsym hd hzsub hdefsub)
      right_add := shiftedInverse_spec _ _ _ _ _
      right_sub := shiftedInverse_spec _ _ _ _ _
      norm_add := norm_shiftedInverse_le _ _ _ _ _
      norm_sub := norm_shiftedInverse_le _ _ _ _ _ }

end Brockian.Weyl.ClosedShiftedRanges

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
  Rellich.lean — the concrete weighted-Rellich estimate.

  A family of Schwartz functions with `∫ ‖g'‖² + ∫ x²‖g‖² ≤ C` is, in `L²(ℝ)`,
  uniformly close to a *fixed* finite-dimensional space of step functions:

  * the confining weight `x²` controls the mass outside `[-R, R]`;
  * the kinetic term `∫ ‖g'‖²` controls the oscillation of `g` inside each cell
    of a partition of `(-R, R]` into `n` intervals of length `h`.

  Together these give `‖g - s‖²_{L²} ≤ h² ∫‖g'‖² + R⁻² ∫ x²‖g‖²`, where `s` is
  the step function taking on each cell the value of `g` at the right endpoint
  of that cell.  Choosing `R` large and `h` small makes the right-hand side as
  small as desired, uniformly over the family.
-/
import RequestProject.Base

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace

namespace Brockian.Weyl.Rellich

open Brockian.Weyl.SchrodingerMinimal
open Brockian.Weyl.HarmonicOscillator

/-! ### Cauchy–Schwarz for a set integral -/

/-- **Cauchy–Schwarz.** `(∫_I f)² ≤ |I| · ∫_I f²`. -/
