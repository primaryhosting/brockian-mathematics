/-
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
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

namespace CS

/-- A codeword lying in the `head? = some b` part of a set is `b :: its tail`. -/

lemma cons_head_tail_of_head?_eq {b : Bool} {w : List Bool} (hw : w.head? = some b) :
    w = b :: w.tail := by
  cases w with
  | nil => simp at hw
  | cons a t => simp at hw; simp [hw]

/-- Kraft's inequality, with an explicit bound `N` on the codeword lengths,
proved by induction on `N`. -/
