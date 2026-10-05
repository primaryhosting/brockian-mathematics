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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- A two-valued splitting lemma: if a set is infinite, one of the two colour classes
determined by a `Bool`-valued function is infinite. -/

lemma seqSet_antitone {k l : ℕ} (h : k ≤ l) : seqSet c l ⊆ seqSet c k := by
  induction l with
  | zero => simpa using (Nat.le_zero.mp h) ▸ subset_rfl
  | succ n ih =>
    rcases Nat.lt_or_ge k (n + 1) with hk | hk
    · exact (seqSet_succ_subset c n).trans (ih (Nat.lt_succ_iff.mp hk))
    · have : k = n + 1 := le_antisymm h hk
      subst this
      exact subset_rfl

/-- The increasing sequence of chosen elements. -/
