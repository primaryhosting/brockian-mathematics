/-
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory

set_option autoImplicit false

namespace Frontier

/--
**Gagliardo–Nirenberg (base case, `n = 1`, `p = 1`).**

If `u : ℝ → ℝ` is everywhere differentiable with derivative `u'`, `u'` is integrable, and `u`
has compact support, then

`‖u‖_{L^∞} ≤ (1/2) * ‖u'‖_{L^1}`,

pointwise: `|u x| ≤ (1/2) * ∫ t, |u' t|` for every `x`.

This is the one-dimensional endpoint case of the Gagliardo–Nirenberg–Sobolev inequality: it is
obtained by writing `u x` both as `∫_{-S}^{x} u'` and as `-∫_{x}^{S} u'` (where `[-S, S]` contains
the support of `u`), and adding the two resulting bounds.  The constant `1/2` is sharp.
-/

theorem nirenberg_gagliardo_L2
    {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Integrable u')
    (hu'sq : Integrable fun t => u' t ^ 2)
    (hsupp : HasCompactSupport u) (x : ℝ) :
    |u x| ^ 2 ≤ Real.sqrt (∫ t, u t ^ 2) * Real.sqrt (∫ t, u' t ^ 2) := by
  have hcont : Continuous u := continuous_iff_continuousAt.mpr fun y => (hu y).continuousAt
  obtain ⟨C, hC⟩ := hsupp.exists_bound_of_continuous hcont
  have hsuppsq : HasCompactSupport fun t => |u t| ^ 2 := by
    apply hsupp.comp_left (g := fun y : ℝ => |y| ^ 2)
    simp
  have husq : Integrable fun t => |u t| ^ 2 :=
    (by fun_prop : Continuous fun t => |u t| ^ 2).integrable_of_hasCompactSupport hsuppsq
  have hu'sq' : Integrable fun t => |u' t| ^ 2 := by simpa [sq_abs] using hu'sq
  have hmul : Integrable fun t => |u t| * |u' t| :=
    hu'.abs.bdd_mul (c := C) (by fun_prop)
      (Filter.Eventually.of_forall fun t => by simpa using hC t)
  have hcs := integral_mul_le_sqrt_mul_sqrt husq hu'sq' hmul
  simp only [sq_abs] at hcs
  exact le_trans (nirenberg_gagliardo_sq hu hu' hsupp x) hcs

end Frontier

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

