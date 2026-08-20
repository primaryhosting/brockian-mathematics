/-
# Mean Value
Category: Pure Mathematics
Target: Math.mean_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Set

namespace Math

/-- The auxiliary function used in the proof of the Mean Value Theorem: `f` corrected by the
linear function with slope `(f b - f a) / (b - a)`. -/
noncomputable def mvtAux (f : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ :=
  fun x => f x - ((f b - f a) / (b - a)) * x

/-- The auxiliary function takes the same value at the two endpoints. -/
theorem mvtAux_endpoints {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) :
    mvtAux f a b a = mvtAux f a b b := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  simp only [mvtAux]
  field_simp
  ring

/-- The auxiliary function is continuous on `[a, b]` whenever `f` is. -/
theorem mvtAux_continuousOn {f : ℝ → ℝ} {a b : ℝ} (hfc : ContinuousOn f (Icc a b)) :
    ContinuousOn (mvtAux f a b) (Icc a b) :=
  hfc.sub ((continuous_const.mul continuous_id).continuousOn)

/-- At each interior point where `f` is differentiable, the auxiliary function has derivative
`deriv f x - (f b - f a) / (b - a)`. -/
theorem mvtAux_hasDerivAt {f : ℝ → ℝ} {a b : ℝ} (hfd : DifferentiableOn ℝ f (Ioo a b))
    {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt (mvtAux f a b) (deriv f x - (f b - f a) / (b - a)) x := by
  have hf : HasDerivAt f (deriv f x) x :=
    ((hfd x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  simpa using hf.sub (((hasDerivAt_id x).const_mul ((f b - f a) / (b - a))))

/-- **Lagrange's Mean Value Theorem.** If `a < b`, `f` is continuous on `[a, b]` and
differentiable on the open interval `(a, b)`, then there is a point `c ∈ (a, b)` with
`deriv f c = (f b - f a) / (b - a)`.

The proof is the classical one: apply Rolle's theorem to `f` corrected by the linear function
of slope `(f b - f a) / (b - a)`. -/
theorem mean_value {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Icc a b)) (hfd : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) := by
  obtain ⟨c, hc, hc0⟩ :=
    exists_hasDerivAt_eq_zero (f := mvtAux f a b)
      (f' := fun x => deriv f x - (f b - f a) / (b - a)) hab (mvtAux_continuousOn hfc)
      (mvtAux_endpoints hab) (fun x hx => mvtAux_hasDerivAt hfd hx)
  exact ⟨c, hc, by linarith [hc0]⟩

/-- Version for a globally differentiable function: if `f : ℝ → ℝ` is differentiable and
`a < b`, then there is `c ∈ (a, b)` with `deriv f c = (f b - f a) / (b - a)`. -/
theorem mean_value_of_differentiable {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : Differentiable ℝ f) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  mean_value hab hf.continuous.continuousOn hf.differentiableOn

end Math

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

