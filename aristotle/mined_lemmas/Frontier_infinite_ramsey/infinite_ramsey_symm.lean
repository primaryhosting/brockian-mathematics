/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
Mathlib (as of this version) contains no infinite Ramsey theorem — searching for `Ramsey`
turns up only `Mathlib/Combinatorics/Hindman.lean` and `Mathlib/Combinatorics/HalesJewett.lean`,
where the word occurs in comments.  So we prove it from scratch, using the classical
ultrafilter argument based on `Filter.hyperfilter`.
-/

namespace Frontier

open Filter Set

noncomputable section

/-- A choice of element of a set of naturals (junk value `0` for the empty set). -/

theorem infinite_ramsey_symm (C : ℕ → ℕ → Bool) (hsymm : ∀ i j, C i j = C j i) :
    ∃ (S : Set ℕ) (c : Bool), S.Infinite ∧ ∀ i ∈ S, ∀ j ∈ S, i ≠ j → C i j = c := by
  obtain ⟨S, c, hinf, hmono⟩ := infinite_ramsey C
  refine ⟨S, c, hinf, ?_⟩
  intro i hi j hj hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hmono i hi j hj h
  · rw [hsymm]; exact hmono j hj i hi h

end Frontier

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

