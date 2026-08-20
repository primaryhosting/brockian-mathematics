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
## Communication complexity of set disjointness

We set up the standard two-party communication model (protocol trees), prove the
rectangle property of transcripts, and deduce the fooling-set lower bound
`n ≤ depth` for any deterministic protocol computing set disjointness on subsets
of `Fin n`.  We then lift this to public-coin randomized protocols.

Scope of the randomized statement: `CS.disjointness_lb` shows that every
public-coin randomized protocol for set disjointness on `Fin n` whose per-input
error probability `ε` satisfies `ε * 4 ^ n < 1` needs at least `n` bits of
communication.  This covers in particular zero-error (Las Vegas) randomized
protocols.  The constant-error version of the bound (Kalyanasundaram–Schnitger,
Razborov), which needs the corruption/information-complexity machinery, is *not*
formalized here.
-/

namespace CS

universe u v

variable {X : Type u} {Y : Type v}

/-- A deterministic two-party communication protocol with Boolean output:
a binary tree whose internal nodes are labelled by the party that speaks
(`alice` sends a bit depending on her input `x`, `bob` on his input `y`). -/
inductive Protocol (X : Type u) (Y : Type v) where
  | leaf (o : Bool) : Protocol X Y
  | alice (f : X → Bool) (a b : Protocol X Y) : Protocol X Y
  | bob (g : Y → Bool) (a b : Protocol X Y) : Protocol X Y

namespace Protocol

/-- The communication cost (worst-case number of exchanged bits) of a protocol. -/

def run : Protocol X Y → X → Y → Bool
  | leaf o, _, _ => o
  | alice f a b, x, y => if f x then a.run x y else b.run x y
  | bob g a b, x, y => if g y then a.run x y else b.run x y

/-- The transcript (sequence of exchanged bits) of the protocol on a pair of inputs. -/
