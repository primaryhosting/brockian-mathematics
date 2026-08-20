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
Weyl's criterion for equidistribution modulo one, and its application to the
sequence `n ↦ n • α` for irrational `α`.
-/
import Mathlib

open Filter MeasureTheory Metric Set Submodule
open scoped Topology Real

namespace Brockian.Equidistribution

noncomputable section

/-! ## Definitions -/

/-- A sequence `u : ℕ → ℝ` is *equidistributed modulo one* if for every subinterval
`[a, b) ⊆ [0, 1]` the proportion of the first `N` terms whose fractional part lies in `[a, b)`
tends to `b - a`. -/

lemma avg_span (hweyl : ∀ h : ℤ, h ≠ 0 → Tendsto (weylSum u h) atTop (𝓝 0))
    (f : C(UnitAddCircle, ℂ)) (hf : f ∈ span ℂ (range (fourier (T := 1)))) :
    Tendsto (avg u f) atTop (𝓝 (∫ z : UnitAddCircle, f z)) := by
  induction hf using Submodule.span_induction with
  | mem x hx => obtain ⟨n, rfl⟩ := hx; exact avg_fourier u hweyl n
  | zero =>
      have h1 : avg u ⇑(0 : C(UnitAddCircle, ℂ)) = fun _ => (0 : ℂ) := by
        funext N; simp [avg]
      rw [h1]; simp
  | add x y hx hy ihx ihy =>
      have hint : ∫ z : UnitAddCircle, (x + y) z = (∫ z, x z) + ∫ z, y z := by
        simpa using integral_add (integrable_of_continuous x) (integrable_of_continuous y)
      have h1 : avg u ⇑(x + y) = fun N => avg u ⇑x N + avg u ⇑y N := by
        funext N
        simp only [avg, ContinuousMap.coe_add, Pi.add_apply, Finset.sum_add_distrib, mul_add]
      rw [hint, h1]
      exact ihx.add ihy
  | smul c x hx ihx =>
      have hint : ∫ z : UnitAddCircle, (c • x) z = c * ∫ z, x z := by
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        exact MeasureTheory.integral_const_mul c _
      have h1 : avg u ⇑(c • x) = fun N => c * avg u ⇑x N := by
        funext N
        simp only [avg, ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        ring
      rw [hint, h1]
      exact ihx.const_mul c

