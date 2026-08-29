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
# Config Count Density Of BV
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_density_of_BV
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory Filter Topology Set

namespace Brockian.EquidistributionBVReduction

open scoped Classical in
/-- `configCount x A N` is the number of indices `n < N` whose orbit point `x n`,
reduced mod `1`, lands in the configuration set `A`. -/

theorem configCount_density_Ici (x : ℕ → ℝ) (hx : EquidistributedMod1 x) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) :
    Tendsto (fun N : ℕ => (configCount x (Set.Ici c) N : ℝ) / N) atTop (𝓝 (1 - c)) := by
  have hset : Set.Ici c ∩ Set.Ioc (0:ℝ) 1 = Set.Icc c 1 := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc, Set.mem_Icc]
    constructor
    · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, h2⟩
  have hvol : volume.real (Set.Ici c ∩ Set.Ioc (0:ℝ) 1) = 1 - c := by
    rw [hset]
    simp [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal, sub_nonneg.2 hc1]
  have := configCount_density_of_BV_measure x hx (Set.Ici c) measurableSet_Ici
    (boundedVariationOn_of_monotoneOn_Icc01 (monotoneOn_indicator_Ici c))
  rwa [hvol] at this

end Brockian.EquidistributionBVReduction

