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
namespace GaleStewart

variable {A : Type*} [Inhabited A]

/-- The initial segment of a play `f` of length `n`, padded with `default`. -/

def Succ (c : ℕ → (ℕ → A) → A) (q p : ℕ × (ℕ → A)) : Prop :=
  ¬ Good W p.1 p.2 ∧ q.1 = p.1 + 1 ∧
    (if Even p.1 then q.2 = Function.update p.2 p.1 (c p.1 p.2)
      else ∃ a : A, q.2 = Function.update p.2 p.1 a)

/-- Player I wins from the position `p` when there is a move-choice function `c` for which
the tree of plays following `c` from `p` and avoiding good positions is well-founded, i.e.
Player I can force reaching a good position in finitely many moves. -/
