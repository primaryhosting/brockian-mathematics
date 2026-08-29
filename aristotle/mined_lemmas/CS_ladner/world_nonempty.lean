/-
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
This file formalizes Ladner's theorem: *if `P ≠ NP` then there are `NP`-intermediate
languages*, i.e. languages that are in `NP`, not in `P`, and not `NP`-complete.

The proof is Ladner's delayed ("lazy") diagonalization: one builds a nondecreasing "hole"
function `hole : ℕ → ℕ` and looks at the language

  `A = K ∩ { x | hole (bit length of x) is even }`,

where `K` is an `NP`-complete language.  While `hole` sits at an even value `2 i` the
construction searches, with a growing step budget, for an input on which the `i`-th
polynomial-time machine disagrees with `A`; while it sits at an odd value `2 j + 1` it
searches for an input witnessing that the `j`-th polynomial-time function fails to reduce
`K` to `A`.  Each time such a witness is found the hole function moves on to the next stage.

If `hole` were bounded it would be eventually constant, and then either `A` would be decided
by a polynomial-time machine while differing from `K` only on finitely many inputs (even
case), or `A` would be finite while `K` reduces to it (odd case); both put `K` in `P`,
contradicting `P ≠ NP`.  Hence `hole` is unbounded, and therefore no machine decides `A` and
no polynomial-time function reduces `K` to `A`; that is, `A` is `NP`-intermediate.

The classes `P` and `NP` are not available in Mathlib, so they are axiomatized here by the
structure `CS.World`, which collects exactly the properties of `P`, `NP`, polynomial-time
many-one reductions, machine enumerations and step-bounded simulations that the argument
uses.  Section "A model" builds an explicit `World`, so that the axiom system is consistent
(of course no `World` with `inP ≠ inNP` can be exhibited, since `P` vs `NP` is open).
-/

namespace CS

/-- A language is a Boolean predicate on `ℕ`; inputs (strings) are encoded as natural
numbers, and `Nat.size x` is the bit length of the input `x`. -/
abbrev Lang := ℕ → Bool

/-- The bit length of `x` is at most `x`. -/

theorem world_nonempty : Nonempty World := ⟨Model.world⟩

end CS

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

