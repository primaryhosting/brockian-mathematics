/-
# In Scope Encoding Complete
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_complete
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# In Scope Encoding Complete
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_complete
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

namespace PCA.Isolation

/-- A request made by a sandboxed app: a resource together with a write flag
(`write = false` means read-only access). -/
structure Request (R : Type*) where
  resource : R
  write : Bool
  deriving DecidableEq

/-- A *scope* granted to a sandboxed app is the set of resources it may touch. -/
abbrev Scope (R : Type*) := Set R

variable {R : Type*}

/-- A request is *in scope* when the resource it names belongs to the granted scope. -/

def decodeRequest (s : Scope R) [DecidablePred (· ∈ s)] (n : ℕ) : Option (Request R) :=
  (Encodable.decode (α := R) (Nat.unpair n).1).bind fun r =>
    if r ∈ s then some ⟨r, decide ((Nat.unpair n).2 = 1)⟩ else none

/-- **Completeness of the in-scope encoding.** Every request that lies inside the
granted scope survives the engine's encode/decode round trip: no in-scope request
is ever rejected or altered by the isolation boundary.

The key ingredient is Mathlib's `Encodable.encodek` (`decode (encode a) = some a`),
together with `Nat.unpair_pair`. -/
