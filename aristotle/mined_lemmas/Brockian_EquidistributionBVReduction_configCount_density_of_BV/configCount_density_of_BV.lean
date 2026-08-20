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
# Equidistribution and the bounded-variation reduction for configuration counts

Let `u : ℕ → ℝ` be a sequence which is *equidistributed* in the unit interval, in the sense
that averages of continuous test functions along `u` converge to the corresponding integral
over `[0,1]` (`Brockian.EquidistributionBVReduction.Equidistributed`).

The main result, `Brockian.EquidistributionBVReduction.configCount_density_of_BV`, upgrades
this from continuous test functions to the indicator of an interval `[a, b) ⊆ [0,1]`, which is
the basic function of bounded variation: the number of indices `n < N` with `u n ∈ [a, b)`
has density `b - a`.

The proof is the usual sandwich argument: the indicator of `[a, b)` is squeezed between two
continuous functions (produced by Urysohn's lemma) whose integrals differ from `b - a` by an
arbitrarily small amount.
-/

open MeasureTheory Set Filter Topology

namespace Brockian
namespace EquidistributionBVReduction

open Classical in
/-- `configCount u S N` is the number of indices `n < N` for which `u n` lies in `S`. -/

theorem configCount_density_of_BV (u : ℕ → ℝ) (hequi : Equidistributed u) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ => (configCount u (Ico a b) N : ℝ) / N) atTop (𝓝 (b - a)) := by
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  have hδ : 0 < ε / 4 := by linarith
  have hup := eventually_configCount_div_le u hequi hab hδ
  have hlo := eventually_le_configCount_div u hequi ha hb hδ
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hup.and hlo)
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN₀ n hn
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end EquidistributionBVReduction
end Brockian

