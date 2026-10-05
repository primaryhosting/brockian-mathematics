/-
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
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

variable {A : Type*}

/-- The finite position consisting of the first `n` moves of the play `x`. -/

lemma extends_append_singleton {p : List A} {a : A} {x : ℕ → A}
    (hp : Extends p x) (ha : x p.length = a) : Extends (p ++ [a]) x := by
  intro i hi
  rw [List.length_append, List.length_singleton] at hi
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h | h
  · rw [hp i h, List.getElem_append_left h]
  · subst h
    rw [ha]
    simp

end Basic

section NoWin

variable (W : Set (ℕ → A))

/-- If Player I has no winning strategy from an even-length position `p` (so it is Player I's
turn), then he has no winning strategy from any one-move extension of `p`. -/
