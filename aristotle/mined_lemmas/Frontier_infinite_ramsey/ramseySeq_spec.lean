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

lemma ramseySeq_spec (U : Ultrafilter ℕ) (hcof : ∀ N : ℕ, {m : ℕ | N < m} ∈ U)
    (hA : A ∈ U) (hAcol : ∀ n ∈ A, {m : ℕ | c n m = k} ∈ U) {i j : ℕ} (hij : i < j) :
    c (ramseySeq c k A i) (ramseySeq c k A j) = k ∧
      ramseySeq c k A i < ramseySeq c k A j := by
  have hmem : ramseySeq c k A j ∈ ramseySets c k A j :=
    ramseySeq_mem U hcof hA hAcol j
  have hsub : ramseySets c k A j ⊆ ramseySets c k A (i + 1) :=
    ramseySets_antitone c k A hij
  have := hsub hmem
  rw [ramseySets] at this
  exact this.2

end RamseyConstruction

/-- **Infinite Ramsey theorem** for pairs and two colours: for every colouring `c`
of the (unordered) pairs of natural numbers by two colours there is an infinite set `S`
all of whose pairs receive the same colour `k`. -/
