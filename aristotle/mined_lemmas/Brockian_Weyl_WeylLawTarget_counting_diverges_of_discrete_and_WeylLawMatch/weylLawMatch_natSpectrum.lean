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

open Filter Topology Set

namespace Brockian.Weyl.WeylLawTarget

/-- The spectral counting function of a set `S ⊆ ℝ` (thought of as the spectrum of an
operator, listed without multiplicity): `spectralCounting S t` is the number of spectral
points that are `≤ t`. -/

theorem weylLawMatch_natSpectrum : WeylLawMatch natSpectrum 1 2 := by
  have hlim : Tendsto (fun t : ℝ => ((⌊t⌋₊ : ℝ) + 1) / t) atTop (𝓝 1) := by
    have h1 : Tendsto (fun t : ℝ => 1 + 1 / t) atTop (𝓝 1) := by
      simpa [one_div] using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℝ))).add
        tendsto_inv_atTop_zero
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [le_div_iff₀ ht]
      linarith [Nat.lt_floor_add_one t]
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have hmul : (1 + 1 / t) * t = t + 1 := by field_simp
      rw [div_le_iff₀ ht, hmul]
      linarith [Nat.floor_le ht.le]
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [spectralCounting_natSpectrum ht]
  norm_num

/-- The hypotheses of `counting_diverges_of_discrete_and_WeylLawMatch` are satisfiable. -/
