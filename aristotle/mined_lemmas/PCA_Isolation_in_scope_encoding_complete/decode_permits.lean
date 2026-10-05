/-!
# In Scope Encoding Complete
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_complete
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA
namespace Isolation

/-- Operations a proof-carrying app may request on a resource. -/
inductive Op
  | read
  | write
  | exec
  deriving DecidableEq, Repr

/-- A request made by an app: a resource path together with the operation. -/
structure Request where
  path : List String
  op : Op
  deriving DecidableEq, Repr

/-- A capability grant: a scope (a path prefix) and the operations allowed inside it. -/
structure Grant where
  scope : List String
  ops : List Op
  deriving DecidableEq, Repr

/-- An isolation policy is a list of grants. -/
abbrev Policy := List Grant

/-- The isolation engine's decision procedure: a request is permitted iff some
grant of the policy covers its path (as a prefix) and allows its operation. -/

theorem decode_permits (pol : Policy) (e : Encoded) (req : Request)
    (h : decode pol e = some req) : permits pol req = true := by
  classical
  unfold decode at h
  by_cases hc : e.grant ∈ pol ∧ e.op ∈ e.grant.ops
  · rw [if_pos hc] at h
    have hreq : req = { path := e.grant.scope ++ e.rel, op := e.op } := (Option.some_inj.1 h).symm
    rw [permits_iff_inScope]
    exact ⟨e.grant, hc.1, by simp [hreq], by simp [hreq, hc.2]⟩
  · rw [if_neg hc] at h
    exact absurd h (by simp)

end Isolation
end PCA

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

