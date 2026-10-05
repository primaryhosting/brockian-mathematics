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
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

open Filter Topology MeasureTheory Complex

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian.Equidistribution

/-! ## Weyl averages of continuous functions on the circle -/

/-- The `N`-th Weyl average of a continuous function `f` on the circle `ℝ / ℤ`, sampled along the
orbit `n ↦ n • α` of the rotation by `α`. -/

noncomputable def weylGood (α : ℝ) : Submodule ℂ C(AddCircle (1 : ℝ), ℂ) where
  carrier := {f | Tendsto (weylAvg α f) atTop (𝓝 (∫ x, f x))}
  zero_mem' := by
    have h : weylAvg α 0 = fun _ : ℕ => (0 : ℂ) := by funext N; simp [weylAvg]
    simp only [Set.mem_setOf_eq, h]
    simp
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq] at *
    have hint : ∫ x, (f + g) x = (∫ x, f x) + ∫ x, g x := by
      simpa using integral_add (circle_integrable f) (circle_integrable g)
    have heq : weylAvg α (f + g) = fun N => weylAvg α f N + weylAvg α g N := by
      funext N; simp [weylAvg, Finset.sum_add_distrib, mul_add]
    rw [hint, heq]
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    simp only [Set.mem_setOf_eq] at *
    have hint : ∫ x, (c • f) x = c * ∫ x, f x := by
      simpa [smul_eq_mul] using integral_smul c fun x => f x
    have heq : weylAvg α (c • f) = fun N => c * weylAvg α f N := by
      funext N
      simp only [weylAvg, ContinuousMap.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      ring
    rw [hint, heq]
    exact hf.const_mul c

