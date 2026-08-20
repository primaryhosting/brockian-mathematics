/-
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Statement: Set-disjointness has Ω(n) randomized communication complexity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Statement: Set-disjointness has Ω(n) randomized communication complexity.
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

/-! ## The communication model

A two-party deterministic communication protocol on inputs `X` (Alice) and `Y` (Bob) is a
binary tree.  At an `alice` node the bit sent depends only on Alice's input, at a `bob` node
only on Bob's input, and a `leaf` carries the output of the protocol.  The `cost` of a protocol
is the depth of the tree, i.e. the number of bits exchanged in the worst case. -/
inductive Protocol (X Y : Type) : Type
  | leaf : Bool → Protocol X Y
  | alice : (X → Bool) → Protocol X Y → Protocol X Y → Protocol X Y
  | bob : (Y → Bool) → Protocol X Y → Protocol X Y → Protocol X Y

namespace Protocol

variable {X Y : Type}

/-- The output of a protocol on a given pair of inputs. -/

theorem disjointness_ub (n : ℕ) :
    ∃ P : Protocol (Inp n) (Inp n), P.cost = n + 1 ∧ ∀ x y : Inp n, P.run x y = Disj x y := by
  refine ⟨reveal n n ∅, reveal_cost n n ∅, ?_⟩
  intro x y
  rw [reveal_run]
  have hx : x.filter (fun i : Fin n => (i : ℕ) < n) = x := by
    apply Finset.filter_true_of_mem
    intro i _
    exact i.isLt
  rw [hx]
  simp [Disj]

end CS

