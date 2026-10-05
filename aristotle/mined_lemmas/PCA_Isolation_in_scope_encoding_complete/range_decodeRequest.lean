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

theorem range_decodeRequest (s : Scope R) [DecidablePred (· ∈ s)] (req : Request R) :
    (∃ n : ℕ, decodeRequest s n = some req) ↔ InScope s req :=
  ⟨fun ⟨_, hn⟩ => decode_in_scope s hn, fun h => ⟨encodeRequest req,
    in_scope_encoding_complete s req h⟩⟩

end PCA.Isolation

