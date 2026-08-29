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

def encodeRequest (req : Request R) : ℕ :=
  Nat.pair (Encodable.encode req.resource) (cond req.write 1 0)

/-- The isolation engine's decoder, *relative to a granted scope*: a code is
accepted only if it names a decodable resource lying inside the scope. -/
