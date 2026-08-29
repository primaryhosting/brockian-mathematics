import Mathlib
/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal NNReal BoundedContinuousFunction

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

namespace Math2

open MeasureTheory Filter Topology Set

/-! ## The Sato–Tate measure -/

/-- The Sato–Tate measure on `ℝ`: the probability measure supported on `[0, π]` with
density `(2/π) · sin²θ` with respect to Lebesgue measure. -/

theorem angleEmpirical_apply (θ : ℕ → ℝ) (X : ℕ) (hX : (Nat.primesBelow X).card ≠ 0)
    {s : Set ℝ} (hs : MeasurableSet s) :
    angleEmpirical θ X s =
      ((Nat.primesBelow X).filter (fun p => θ p ∈ s)).card / ((Nat.primesBelow X).card : ℝ≥0∞) := by
  rw [angleEmpirical, if_neg hX, Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply]
  simp only [MeasureTheory.Measure.dirac_apply' _ hs, Set.indicator_apply, Pi.one_apply]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  simp [smul_eq_mul, ENNReal.div_eq_inv_mul]

instance (θ : ℕ → ℝ) (X : ℕ) : IsProbabilityMeasure (angleEmpirical θ X) := by
  constructor
  by_cases hX : (Nat.primesBelow X).card = 0
  · rw [angleEmpirical, if_pos hX]
    simp
  · rw [angleEmpirical_apply θ X hX MeasurableSet.univ]
    simp only [Set.mem_univ, Finset.filter_true]
    exact ENNReal.div_self (by exact_mod_cast hX) (ENNReal.natCast_ne_top _)

/-- The empirical distribution as a bundled probability measure. -/
