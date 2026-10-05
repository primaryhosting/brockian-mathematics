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

theorem counting_diverges_of_rvm_asymptotic
    (S : Set ℝ)
    (hrvm : Filter.Tendsto (fun T : ℝ => (counting S T : ℝ) / rvmMainTerm T)
      Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun T : ℝ => (counting S T : ℝ)) Filter.atTop Filter.atTop := by
  have hmain := rvmMainTerm_tendsto_atTop
  have hprod := hrvm.pos_mul_atTop one_pos hmain
  refine hprod.congr' ?_
  have hne : ∀ᶠ T : ℝ in Filter.atTop, rvmMainTerm T ≠ 0 := by
    filter_upwards [hmain.eventually_gt_atTop 0] with T hT using ne_of_gt hT
  filter_upwards [hne] with T hT
  field_simp

end Brockian.Weyl.WeylLawTarget

