import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
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

set_option grind.warning false

namespace Brockian.Equidistribution

open MeasureTheory Filter Topology Metric Finset

noncomputable section

local notation "𝕋" => AddCircle (1 : ℝ)

/-! ### Cesàro averages along a sequence -/

/-- The Cesàro average of a function `f` on the circle `ℝ/ℤ` along the first `N` terms of a
real sequence `x`. -/

theorem equidistribution_nat_mul_irrational {α : ℝ} (hα : Irrational α) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ =>
        ((((Finset.range N).filter
          (fun n : ℕ => Int.fract ((n : ℝ) * α) ∈ Set.Ico a b)).card : ℝ)) / N)
      atTop (𝓝 (b - a)) :=
  equidistribution_of_asymptotic (fun n => (n : ℝ) * α)
    (fun h hh => weyl_sums_tendsto_zero_of_irrational hα h hh) ha hab hb

end

end Brockian.Equidistribution

