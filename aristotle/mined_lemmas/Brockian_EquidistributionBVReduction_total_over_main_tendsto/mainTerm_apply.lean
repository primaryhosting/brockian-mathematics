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

open Filter Topology

namespace Brockian.EquidistributionBVReduction

/-- The *main term* of a Koksma-type (bounded-variation) equidistribution estimate:
for a sequence of length `N` and a mean value `I` (typically `I = ∫ x in (0:ℝ)..1, f x`),
the main term is `N * I`. -/

theorem mainTerm_apply (I : ℝ) (N : ℕ) : mainTerm I N = (N : ℝ) * I := rfl

/-- The relative error of a Koksma-type estimate tends to `0`.

If the total sum `total N` differs from the main term `N * I` by at most
`V * N * disc N` (the Koksma–Hlawka bound: total variation `V` times the number of terms
times the discrepancy `disc N`) and the discrepancy tends to `0` (equidistribution),
then `(total N - mainTerm I N) / mainTerm I N → 0`. -/
