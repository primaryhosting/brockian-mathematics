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
# Counting Diverges Of Candidate
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_candidate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Counting Diverges Of Candidate
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_candidate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian.Weyl.WeylLawTarget

open Filter Set

/-- A *candidate spectrum* for a Weyl law: a nondecreasing sequence of real
"eigenvalues" that tends to `+∞`. -/
structure Candidate where
  /-- The eigenvalue sequence. -/
  lam : ℕ → ℝ
  /-- The eigenvalues are listed in nondecreasing order. -/
  mono : Monotone lam
  /-- The eigenvalues tend to `+∞` (discreteness of the spectrum). -/
  tendsto_atTop : Filter.Tendsto lam Filter.atTop Filter.atTop

/-- The eigenvalue counting function `N(t) = #{n : λ n ≤ t}` of a candidate spectrum. -/

theorem counting_diverges_of_candidate (C : Candidate) :
    Filter.Tendsto (fun t : ℝ => counting C t) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 fun m => ?_
  filter_upwards [Filter.eventually_ge_atTop (C.lam m)] with t ht
  exact le_trans (Nat.le_succ m) (le_counting C m ht)

end Brockian.Weyl.WeylLawTarget

