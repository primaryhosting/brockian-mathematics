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
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Brockian
namespace EquidistributionBVReduction

/-- **Total over main tendsto.**

In the bounded-variation reduction step of an equidistribution argument one writes a
total quantity as `main + err`, where the error term is asymptotically negligible
compared with the main term.  Under exactly these hypotheses — the main term is
eventually nonzero, and `err = o(main)` — the ratio of the total to the main term
tends to `1`. -/

theorem total_div_main_tendsto {total main : ℕ → ℝ}
    (hne : ∀ᶠ N in atTop, main N ≠ 0)
    (hlo : (fun N => total N - main N) =o[atTop] main) :
    Tendsto (fun N => total N / main N) atTop (𝓝 1) := by
  have h := total_over_main_tendsto hne hlo
  refine h.congr fun N => ?_
  ring_nf

/-- Concrete instance: if the Cesàro averages of `f` converge to a nonzero mean `I`,
then the total sum divided by the main term `N * I` tends to `1`. -/
