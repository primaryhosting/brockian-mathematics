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
# Counting Diverges Of Discrete And Weyl Law Match
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_WeylLawMatch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology

namespace Brockian.Weyl.WeylLawTarget

/-- The eigenvalue counting function of a spectrum `S ⊆ ℝ`:
`countingFunction S t` is the number of points of `S` that are `≤ t`
(with the convention `ncard = 0` for infinite sets). -/

theorem discrete_and_weylLawMatch_natRange :
    DiscreteSpectrum (Set.range ((↑) : ℕ → ℝ)) ∧
      WeylLawMatch (Set.range ((↑) : ℕ → ℝ)) 2 1 := by
  refine ⟨fun t => Set.Finite.subset ((Set.finite_Iic _).image _) (natRange_inter_Iic_subset t),
    one_pos, two_pos, ?_⟩
  have hfloor : Tendsto (fun t : ℝ => ((⌊t⌋₊ : ℝ) + 1) / t) atTop (𝓝 1) := by
    have hinv : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) := by
      simpa [one_div] using (tendsto_inv_atTop_zero (𝕜 := ℝ))
    have h1 : Tendsto (fun t : ℝ => (t + 1) / t) atTop (𝓝 1) := by
      have heq : (fun t : ℝ => 1 + 1 / t) =ᶠ[atTop] fun t : ℝ => (t + 1) / t := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
        field_simp
      refine Tendsto.congr' heq ?_
      simpa using (tendsto_const_nhds (X := ℝ) (α := ℝ) (x := (1 : ℝ)) (f := atTop)).add hinv
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds (X := ℝ) (α := ℝ) (x := (1 : ℝ)) (f := atTop)) h1 ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [le_div_iff₀ ht]
      have := Nat.lt_floor_add_one t
      linarith
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      gcongr
      exact Nat.floor_le ht.le
  refine Tendsto.congr' ?_ hfloor
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [countingFunction_natRange t ht.le]
  norm_num [Real.rpow_one]

end Brockian.Weyl.WeylLawTarget

