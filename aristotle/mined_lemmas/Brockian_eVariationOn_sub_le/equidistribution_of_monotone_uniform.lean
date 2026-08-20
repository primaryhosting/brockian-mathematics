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

import Mathlib

/-!
# Reduction of equidistribution mod 1 to test functions of bounded variation

This file contains an unconditional proof that a sequence `x : ℕ → ℝ` whose Cesàro averages
against every test function of bounded variation on `[0,1]` converge to the corresponding
integral is uniformly distributed (equidistributed) mod `1`.

The main statement is `Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform`.
It is deduced from the formally stronger
`Brockian.EquidistributionBVReduction.equidistribution_of_monotone_uniform`, where only
monotone test functions are used.

All auxiliary facts are proved here, with no assumed black boxes; in particular the
subadditivity of the (extended) variation with respect to differences of functions,
the bounded variation of indicator functions of intervals, and the relevant integrals.
-/

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace Brockian
namespace EquidistributionBVReduction

/-! ## Bounded variation of a step function -/

/-- Subadditivity of the extended variation for a difference of two real valued functions. -/

theorem equidistribution_of_monotone_uniform (x : ℕ → ℝ) (h : MonotoneTestConvergence x) :
    EquidistributedMod1 x := by
  intro a b ha hab hb
  have hA := h (step a) ((monotone_step a).monotoneOn _)
  have hB := h (step b) ((monotone_step b).monotoneOn _)
  rw [integral_step a ha (hab.trans hb)] at hA
  rw [integral_step b (ha.trans hab) hb] at hB
  have hsub := hA.sub hB
  have hfract : ∀ n : ℕ, Int.fract (x n) ∈ Set.Icc (0:ℝ) 1 := fun n =>
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hfun : (fun N : ℕ => (∑ n ∈ Finset.range N, step a (Int.fract (x n))) / N
        - (∑ n ∈ Finset.range N, step b (Int.fract (x n))) / N)
      = fun N : ℕ =>
        (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) / N := by
    funext N
    rw [div_sub_div_same, ← Finset.sum_sub_distrib, ← sum_indicator_eq_card x a b N]
    refine congrArg (· / (N : ℝ)) (Finset.sum_congr rfl fun n _ => ?_)
    exact (indicator_Ico_eqOn a b hab (hfract n)).symm
  rw [hfun] at hsub
  have hval : 1 - a - (1 - b) = b - a := by ring
  rwa [hval] at hsub

/-- **Reduction of equidistribution to bounded variation test functions.**
If the Cesàro averages of a sequence against every function of bounded variation on `[0,1]`
converge to the corresponding integral, then the sequence is equidistributed mod `1`. -/
