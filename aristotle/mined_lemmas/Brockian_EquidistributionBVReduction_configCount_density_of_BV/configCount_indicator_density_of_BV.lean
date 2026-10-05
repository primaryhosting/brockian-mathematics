import Mathlib

/-!
# Config Count Density Of BV
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_density_of_BV
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

namespace Brockian
namespace EquidistributionBVReduction

open Filter Set MeasureTheory
open scoped Topology

/-- `configCount f x N` is the number of the first `N` points of the sequence `x`, each
configuration `x n` being counted with the weight `f (x n)`. -/

theorem configCount_indicator_density_of_BV {x : ℕ → ℝ} (hx : ∀ n, x n ∈ Ico (0:ℝ) 1)
    (hequi : Equidistributed x) {A : Set ℝ} (hA : MeasurableSet A)
    (hBV : BoundedVariationOn (A.indicator (fun _ => (1:ℝ))) (Icc (0:ℝ) 1)) :
    Tendsto (fun N : ℕ => (((Finset.range N).filter fun n => x n ∈ A).card : ℝ) / N) atTop
      (𝓝 (volume (A ∩ Ioc (0:ℝ) 1)).toReal) := by
  have hcount : ∀ N : ℕ, configCount (A.indicator (fun _ => (1:ℝ))) x N
      = (((Finset.range N).filter fun n => x n ∈ A).card : ℝ) := by
    intro N
    simp [configCount, Set.indicator_apply]
  have hint : (∫ t in (0:ℝ)..1, A.indicator (fun _ => (1:ℝ)) t)
      = (volume (A ∩ Ioc (0:ℝ) 1)).toReal := by
    rw [intervalIntegral.integral_of_le zero_le_one,
      MeasureTheory.setIntegral_indicator hA, MeasureTheory.setIntegral_const,
      Set.inter_comm]
    simp [MeasureTheory.measureReal_def]
  have := configCount_density_of_BV hx hequi hBV
  rw [hint] at this
  simpa only [hcount] using this

end EquidistributionBVReduction
end Brockian

