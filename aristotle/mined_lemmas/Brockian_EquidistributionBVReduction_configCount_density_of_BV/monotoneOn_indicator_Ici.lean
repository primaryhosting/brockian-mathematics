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

lemma monotoneOn_indicator_Ici (c : ℝ) :
    MonotoneOn ((Set.Ici c).indicator (fun _ => (1:ℝ))) (Set.Icc (0:ℝ) 1) := by
  intro a _ b _ hab
  simp only [Set.indicator_apply, Set.mem_Ici]
  split_ifs with h1 h2 <;> try norm_num
  · linarith

/-- For a half-line configuration `A = [c, ∞)` with `0 < c ≤ 1` the density of the
configuration counts is `1 - c`. -/
