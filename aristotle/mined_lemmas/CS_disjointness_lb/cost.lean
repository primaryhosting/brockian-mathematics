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

/-
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Set disjointness has `Ω(n)` randomized communication complexity

We formalise two-party communication protocols as decision trees (`CS.Protocol`), where
`CS.Protocol.cost` is the depth of the tree, i.e. the worst-case number of bits exchanged.

A *public-coin randomized protocol* is modelled as a finite family `P : Fin m → Protocol X Y`
of deterministic protocols, run under the uniform distribution on `Fin m` (allowing repetitions
in the family, this captures every distribution with rational probabilities).

The main theorem `CS.disjointness_lb` states the `Ω(n)` lower bound for randomized protocols
with *one-sided error* (false-biased protocols): if every protocol in the family is sound
(it never accepts a pair of intersecting sets) and, for every disjoint pair, at least half of
the protocols accept, then some protocol in the family has cost at least `n - 1`.

The engine is the classical fooling-set bound `CS.Protocol.fooling_card_le`, proved by
induction on the protocol tree, together with a double counting argument over the fooling set
`{ (x, xᶜ) : x ∈ {0,1}ⁿ }` of size `2ⁿ`.
-/

namespace CS

variable {X Y : Type*}

/-- A deterministic two-party communication protocol, as a decision tree.
`nodeA g t0 t1` means Alice sends the bit `g x` and the protocol continues in `t1` (if the bit
is `true`) or `t0` (if it is `false`); `nodeB` is the same with Bob speaking. -/
inductive Protocol (X Y : Type*) : Type _
  | leaf : Bool → Protocol X Y
  | nodeA : (X → Bool) → Protocol X Y → Protocol X Y → Protocol X Y
  | nodeB : (Y → Bool) → Protocol X Y → Protocol X Y → Protocol X Y

namespace Protocol

/-- The communication cost of a protocol: the depth of the tree, i.e. the worst-case number of
bits exchanged. -/

def cost : Protocol X Y → ℕ
  | leaf _ => 0
  | nodeA _ t0 t1 => max t0.cost t1.cost + 1
  | nodeB _ t0 t1 => max t0.cost t1.cost + 1

/-- The output of a protocol on a pair of inputs. -/
