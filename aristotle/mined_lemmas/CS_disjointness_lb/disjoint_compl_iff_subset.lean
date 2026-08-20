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

lemma disjoint_compl_iff_subset {n : ℕ} (s t : Inp n) : Disjoint s tᶜ ↔ s ⊆ t := by
  simp only [Finset.disjoint_right, Finset.mem_compl]
  constructor
  · intro h x hx
    by_contra hc
    exact h hc hx
  · intro h x hx hxs
    exact hx (h hxs)

/-- Key counting lemma: if a protocol `P` accepts only disjoint pairs inside the rectangle
`A × B`, then the number of fooling-set elements `(S, Sᶜ)` with `S ∈ A`, `Sᶜ ∈ B` that it
accepts is at most `2 ^ cost P` (the number of leaves of the protocol tree). -/
