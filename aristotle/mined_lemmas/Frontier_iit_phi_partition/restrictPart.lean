import Mathlib

/-!
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## Setting

A *system* consists of a finite set `V` of elements, each of which can be in one of
finitely many states `S`; a global state of the system is a function `V → S`.

The dynamics of the system are given by a transition kernel
`T : (V → S) → (V → S) → ℝ`, where `T s t` is the probability of moving to state `t`
from state `s`.

A *bipartition* of the system is a map `p : V → Bool` which is neither constantly
`true` nor constantly `false`; the two parts are `{v // p v = true}` and
`{v // p v = false}`.

The *effective information* of a bipartition `p` measures how far the dynamics is
from being the product of the dynamics of the two parts taken separately: it is the
(weighted) average over current states `s` of the `ℓ¹`-distance between the true
next-state distribution `T s ·` and the product of its two marginals on the parts.

*Integrated information* `Φ` is the infimum of the effective information over all
bipartitions ("the minimum information partition").

The target theorem states that a system which is *disconnected*, i.e. whose state
space splits into two nonempty parts that evolve independently of one another,
has `Φ = 0`.
-/

section Defs

variable {V S : Type*}

/-- Restriction of a global state `t : V → S` to the part `{v // p v = b}` of the
bipartition `p`. -/

def restrictPart (p : V → Bool) (b : Bool) (t : V → S) : {v // p v = b} → S :=
  fun v => t v.1

/-- Assemble a global state from states of the two parts of the bipartition `p`. -/
