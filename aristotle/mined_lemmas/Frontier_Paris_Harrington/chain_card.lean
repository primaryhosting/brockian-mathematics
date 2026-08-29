import Mathlib

/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
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

/-- A finite set `Y` of positive integers is *relatively large* when its least element is at
most its cardinality. -/

lemma chain_card {k : ℕ} (n : ℕ) (c : Finset ℕ → Fin k) (t : ℕ) :
    (chain n c t).card = t := by
  induction t with
  | zero => simp [chain]
  | succ t ih =>
      rw [chain, Finset.card_insert_of_notMem (next_notMem n c _), ih]

