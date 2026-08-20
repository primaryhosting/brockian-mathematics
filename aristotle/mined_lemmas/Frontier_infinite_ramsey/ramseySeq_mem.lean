import Mathlib

/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

open Filter

section RamseyConstruction

/-- Pick an element of a set of naturals (junk value `0` if the set is empty). -/

lemma ramseySeq_mem (U : Ultrafilter ℕ) (hcof : ∀ N : ℕ, {m : ℕ | N < m} ∈ U)
    (hA : A ∈ U) (hAcol : ∀ n ∈ A, {m : ℕ | c n m = k} ∈ U) (n : ℕ) :
    ramseySeq c k A n ∈ ramseySets c k A n :=
  pick_mem (Ultrafilter.nonempty_of_mem (ramseySets_mem U hcof hA hAcol n).1)

