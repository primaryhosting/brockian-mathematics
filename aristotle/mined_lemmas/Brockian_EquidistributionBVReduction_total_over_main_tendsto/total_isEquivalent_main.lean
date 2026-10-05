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

namespace Brockian
namespace EquidistributionBVReduction

/-- The *total* quantity in a main-term/error-term decomposition: `total main err n`
is the main term `main n` corrected by the error term `err n`. -/

theorem total_isEquivalent_main (main err : ℕ → ℝ) (herr : err =o[atTop] main) :
    (total main err) ~[atTop] main := by
  have h : total main err - main = err := by funext n; simp [total]
  simpa [Asymptotics.IsEquivalent, h] using herr

end EquidistributionBVReduction
end Brockian

