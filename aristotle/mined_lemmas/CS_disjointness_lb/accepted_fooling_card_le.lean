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

lemma accepted_fooling_card_le {n : ℕ} (P : Protocol (Inp n) (Inp n))
    (hsound : ∀ x y : Inp n, P.run x y = true → Disjoint x y) :
    (Finset.univ.filter (fun S : Inp n => P.run S Sᶜ = true)).card ≤ 2 ^ P.cost := by
  have h := fooling_card_le P Finset.univ Finset.univ (fun x _ y _ h => hsound x y h)
  simpa using h

/-! ## The randomized lower bound

A *public-coin randomized protocol* is a family `P : R → Protocol X Y` of deterministic
protocols indexed by a finite nonempty set `R` of random strings, drawn uniformly.

We prove an `Ω(n)` lower bound for randomized protocols with *one-sided* error: the protocol
never accepts a non-disjoint pair, and accepts a disjoint pair with probability at least
`1 / 2`.  (Two-sided error, i.e. Razborov's theorem, is not covered by this argument; indeed
the fooling-set method used here is genuinely unavailable for two-sided error.) -/

/-- General form of the lower bound, with an arbitrary success probability `1 / m`:
if a public-coin randomized protocol never accepts a non-disjoint pair and accepts every
disjoint pair with probability at least `1 / m`, and every protocol of the family costs at
most `c`, then `2 ^ n ≤ m * 2 ^ c`. -/
