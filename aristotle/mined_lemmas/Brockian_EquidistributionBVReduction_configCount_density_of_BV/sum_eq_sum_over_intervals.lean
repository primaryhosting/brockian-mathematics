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

lemma sum_eq_sum_over_intervals {g : ℝ → ℝ} (hx : ∀ n, x n ∈ Ico (0:ℝ) 1) {m : ℕ} (hm : 0 < m)
    (N : ℕ) :
    ∑ n ∈ Finset.range N, g (x n)
      = ∑ i ∈ Finset.range m, ∑ n ∈ (Finset.range N).filter
          (fun n => x n ∈ Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m)), g (x n) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmaps : ∀ n ∈ Finset.range N, ⌊(m : ℝ) * x n⌋₊ ∈ Finset.range m := by
    intro n _
    have h1 : x n < 1 := (hx n).2
    have h0 : (0:ℝ) ≤ x n := (hx n).1
    refine Finset.mem_range.2 ?_
    have hlt : (m : ℝ) * x n < m := by nlinarith
    exact (Nat.floor_lt (by positivity)).2 hlt
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun n => g (x n))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr ?_ (fun n _ => rfl)
  refine Finset.filter_congr (fun n _ => ?_)
  simpa using floor_eq_iff_mem_Ico hm (hx n).1 i

end Aux

section Monotone

variable {x : ℕ → ℝ} {g : ℝ → ℝ}

/-- The integral over `[0,1]` split as a sum of integrals over the `m` intervals
`[i/m, (i+1)/m]`. -/
