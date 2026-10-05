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
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Filter Topology

set_option maxHeartbeats 1000000

namespace Brockian.Weyl.WeylLawTarget

/-- The spectral counting function of a set `S ⊆ ℝ` of spectral points: the number of points
of `S` in the symmetric window `[-T, T]`.

(When `S ∩ [-T, T]` is infinite this is `0` by the junk-value convention of `Set.ncard`;
the discreteness hypothesis below rules that out.) -/

theorem rvmMainTerm_tendsto_atTop :
    Filter.Tendsto rvmMainTerm Filter.atTop Filter.atTop := by
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have hu : Filter.Tendsto (fun T : ℝ => T / (2 * Real.pi)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.2 fun b => ⟨b * (2 * Real.pi), fun T hT => by
      rw [le_div_iff₀ hpi]; exact hT⟩
  have hlog : Filter.Tendsto (fun T : ℝ => Real.log (T / (2 * Real.pi)) - 1)
      Filter.atTop Filter.atTop := by
    have h := Filter.tendsto_atTop_add_const_right _ (-1) (Real.tendsto_log_atTop.comp hu)
    simpa [Function.comp_apply, sub_eq_add_neg] using h
  exact (hu.atTop_mul_atTop₀ hlog).congr fun T => by simp only [rvmMainTerm]; ring

/-- If the counting function of a spectrum obeys the Riemann–von Mangoldt asymptotic
`N(T) ~ (T/2π) log (T/2π) - T/2π`, then it diverges to `+∞`. -/
