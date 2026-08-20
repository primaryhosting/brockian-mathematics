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
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.RuthAaronPairs

/-- `sopfr n` is the sum of the prime factors of `n`, counted with multiplicity
(A001414, the "integer logarithm"). By convention `sopfr 0 = sopfr 1 = 0`. -/

theorem exists_six_ruthAaronPairs :
    ∃ s : Finset ℕ, s.card = 6 ∧ ∀ n ∈ s, IsRuthAaronPair n := by
  refine ⟨{5, 8, 15, 77, 125, 714}, by decide, fun n hn => ?_⟩
  fin_cases hn
  · exact isRuthAaronPair_five
  · exact isRuthAaronPair_eight
  · exact isRuthAaronPair_fifteen
  · exact isRuthAaronPair_seventyseven
  · exact isRuthAaronPair_125
  · exact isRuthAaronPair_714

/-! ### The infinitude statement

Whether there are infinitely many Ruth–Aaron pairs is an open problem (Erdős).
The theorem below is the exact reduction of that conjecture to the statement that
Ruth–Aaron pairs are unbounded; it is proved unconditionally. -/

/-- **Ruth–Aaron infinitude, as an equivalence.** The set of Ruth–Aaron pairs is
infinite if and only if it is unbounded, i.e. iff for every `N` there is a
Ruth–Aaron pair `n > N`. (The truth of either side is the open Erdős conjecture;
this theorem is the unconditional reduction between the two formulations.) -/
