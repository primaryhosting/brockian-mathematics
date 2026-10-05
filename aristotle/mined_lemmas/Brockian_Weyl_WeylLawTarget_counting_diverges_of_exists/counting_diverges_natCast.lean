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
# Counting Diverges Of Exists
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.Weyl.WeylLawTarget

open Filter

/-- The eigenvalue counting function of a sequence `lam : ℕ → ℝ` of eigenvalues
(listed with multiplicity): `counting lam t` is the number of indices `n` with
`lam n ≤ t`. -/

theorem counting_diverges_natCast :
    Filter.Tendsto (counting (fun n : ℕ => (n : ℝ))) Filter.atTop Filter.atTop := by
  refine counting_diverges_of_exists _ (fun t => ?_)
  refine Set.Finite.subset (Set.finite_Iio (⌊t⌋₊ + 1)) ?_
  intro n hn
  have hn' : (n : ℝ) ≤ t := hn
  exact Nat.lt_succ_of_le (Nat.le_floor hn')

end Brockian.Weyl.WeylLawTarget

