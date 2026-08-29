/-!
# In Scope Encoding Sound
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Isolation

/-- A single component of a resource path (e.g. one segment of `"/etc/ssl/certs"`). -/
abbrev Component := String

/-- The actions an application may attempt on a resource. -/
inductive Action where
  | read : Action
  | write : Action
  | exec : Action
  deriving DecidableEq, Repr

/-- A capability grants `action` on every resource under the path prefix `path`. -/
structure Capability where
  action : Action
  path : List Component
  deriving DecidableEq, Repr

/-- A request made by the application: an `action` on the resource at `path`. -/
structure Request where
  action : Action
  path : List Component
  deriving DecidableEq, Repr

/-- The isolation scope of an application: the list of capabilities it was granted. -/
abbrev Scope := List Capability

/-- Declarative semantics of the isolation engine: a request is *in scope* when some granted
capability matches its action and its path prefixes the requested resource path. -/

def sampleScope : Scope :=
  [ { action := Action.read, path := ["etc", "ssl"] },
    { action := Action.write, path := ["tmp"] } ]

example : check sampleScope { action := Action.read, path := ["etc", "ssl", "certs"] } = true := by
  rw [in_scope_encoding_sound]; decide

example : check sampleScope { action := Action.write, path := ["etc", "ssl", "certs"] } = false := by
  rw [check_eq_false_iff]; decide

example : check sampleScope { action := Action.read, path := ["etc"] } = false := by
  rw [check_eq_false_iff]; decide

example : check sampleScope { action := Action.write, path := ["tmp", "a", "b"] } = true := by
  rw [in_scope_encoding_sound]; decide

end PCA.Isolation

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

