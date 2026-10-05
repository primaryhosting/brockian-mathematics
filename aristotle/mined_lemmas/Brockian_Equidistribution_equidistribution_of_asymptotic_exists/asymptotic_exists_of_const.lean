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

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace Brockian.Equidistribution

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

/-- The empirical measure of the first `N + 1` terms of the sequence `x`: the average of the
Dirac masses at `x 0, …, x N`. -/

lemma asymptotic_exists_of_const (c : X) :
    ∀ f : C(X, ℝ), ∃ L : ℝ,
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f ((fun _ : ℕ => c) n)) atTop
        (𝓝 L) := by
  refine fun f => ⟨f c, ?_⟩
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  field_simp
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]

end Brockian.Equidistribution

