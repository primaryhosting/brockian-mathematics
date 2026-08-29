import Mathlib

/-!
# Mean Value
Category: Pure Mathematics
Target: Math.mean_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math

open Set

/-- **Lagrange's Mean Value Theorem**, `HasDerivAt` form.

If `f : ℝ → ℝ` is continuous on `[a, b]` (with `a < b`) and has derivative `f' x` at every
point `x` of the open interval `(a, b)`, then there is a point `c ∈ (a, b)` with
`f' c = (f b - f a) / (b - a)`.

This is derived here from Rolle's theorem by subtracting the secant line. -/
theorem mean_value_hasDerivAt {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Icc a b)) (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a) := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  set m : ℝ := (f b - f a) / (b - a) with hm
  -- the function `f` with the secant line subtracted
  set g : ℝ → ℝ := fun x => f x - m * (x - a) with hg
  set g' : ℝ → ℝ := fun x => f' x - m with hg'
  have hgc : ContinuousOn g (Icc a b) := by
    apply hfc.sub
    exact (continuousOn_const.mul ((continuousOn_id).sub continuousOn_const))
  have hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => m * (y - a)) m x := by
      simpa using ((hasDerivAt_id x).sub_const a).const_mul m
    simpa [hg, hg'] using (hff' x hx).sub h1
  have hgab : g a = g b := by
    have : m * (b - a) = f b - f a := by
      rw [hm]
      field_simp
    simp only [hg]
    rw [this]
    ring
  obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hab hgc hgab hgg'
  refine ⟨c, hc, ?_⟩
  have : f' c - m = 0 := hc0
  linarith

/-- **Mean Value Theorem**.

A function `f : ℝ → ℝ` that is continuous on `[a, b]` (with `a < b`) and differentiable at every
point of the open interval `(a, b)` admits a point `c ∈ (a, b)` such that
`deriv f c = (f b - f a) / (b - a)`. -/
theorem mean_value {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Icc a b)) (hfd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  mean_value_hasDerivAt hab hfc fun x hx => (hfd x hx).hasDerivAt

/-- **Mean Value Theorem** for a globally differentiable function: if `f` is differentiable on all
of `ℝ` and `a < b`, then some `c ∈ (a, b)` satisfies `deriv f c = (f b - f a) / (b - a)`. -/
theorem mean_value_of_differentiable {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : Differentiable ℝ f) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  mean_value hab hf.continuous.continuousOn fun x _ => hf x

end Math

