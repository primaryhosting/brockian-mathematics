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

import Brockian.Weyl.TestFunction

/-!
# The du Bois-Reymond lemmas

A locally integrable function whose distributional derivative vanishes is almost everywhere
constant; a locally integrable function whose distributional second derivative vanishes is
almost everywhere affine.
-/

open MeasureTheory Filter
open scoped Topology ContDiff NNReal

namespace Brockian.Weyl.DeficiencyODE

/-! ## The du Bois-Reymond lemmas -/

/-- **du Bois-Reymond lemma.**  A locally integrable function whose distributional derivative
vanishes is almost everywhere constant. -/

theorem integral_deriv_mul {f g f' g' : ℝ → ℂ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hf' : Continuous f') (hg' : Continuous g')
    (hcs : HasCompactSupport f) :
    ∫ x, f' x * g x = -∫ x, f x * g' x := by
  have hfc : Continuous f := by
    rw [continuous_iff_continuousAt]; exact fun x => (hf x).continuousAt
  have hgc : Continuous g := by
    rw [continuous_iff_continuousAt]; exact fun x => (hg x).continuousAt
  have hf'cs : HasCompactSupport f' := by
    have : f' = deriv f := funext fun x => ((hf x).deriv).symm
    rw [this]; exact hcs.deriv
  have hprod : ∀ x, HasDerivAt (fun y => f y * g y) (f' x * g x + f x * g' x) x :=
    fun x => (hf x).mul (hg x)
  have hcs' : HasCompactSupport (fun y => f y * g y) := hcs.mul_right
  have key := integral_deriv_eq_zero hprod (by fun_prop) hcs'
  have h1 : Integrable (fun x => f' x * g x) :=
    (hf'.mul hgc).integrable_of_hasCompactSupport hf'cs.mul_right
  have h2 : Integrable (fun x => f x * g' x) :=
    (hfc.mul hg').integrable_of_hasCompactSupport hcs.mul_right
  rw [integral_add h1 h2] at key
  linear_combination (norm := ring_nf) key

/-! ## A test function of unit mass, and primitives of test functions -/

/-- There is a test function of integral one. -/
