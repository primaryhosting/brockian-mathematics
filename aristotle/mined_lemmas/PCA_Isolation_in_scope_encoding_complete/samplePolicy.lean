/-!
# In Scope Encoding Complete
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_complete
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Isolation

/-! ## The abstract model

An *isolation engine* mediates every access an application makes to a resource.
Resources are addressed by hierarchical paths (`List String`), and every access
is performed in one of two modes.  A *policy* is a list of capabilities, each of
which grants one mode on a whole subtree of the resource hierarchy.

The engine does not scan the policy list at access time; instead the policy is
*encoded* once into a prefix tree (`Trie`) which the engine then walks.  The
results below relate the declarative notion `InScope` with the operational
notion `engineAccepts` computed on the encoded policy. -/

/-- Access modes mediated by the isolation engine. -/
inductive Mode where
  | read : Mode
  | write : Mode
  deriving DecidableEq, Repr

/-- A capability grants `mode` on every resource at or below the path `root`. -/
structure Capability where
  root : List String
  mode : Mode
  deriving DecidableEq, Repr

/-- An access request: a resource path together with the mode of access. -/
structure Request where
  path : List String
  mode : Mode
  deriving DecidableEq, Repr

/-- A policy is a list of capabilities. -/
abbrev Policy := List Capability

/-- The declarative (model-level) notion of being in scope: some capability of
the policy grants the requested mode on a prefix of the requested path. -/

def samplePolicy : Policy :=
  [⟨["home", "app"], Mode.read⟩, ⟨["tmp"], Mode.write⟩]

example : engineAccepts samplePolicy ⟨["home", "app", "data"], Mode.read⟩ = true := rfl

example : engineAccepts samplePolicy ⟨["home", "app", "data"], Mode.write⟩ = false := rfl

/-- The engine refuses an access outside the granted subtrees, and hence, by
soundness, such an access is genuinely out of scope. -/
example : ¬ InScope samplePolicy ⟨["home", "other"], Mode.read⟩ := by
  intro h
  have h2 := in_scope_encoding_complete _ _ h
  have hfalse : engineAccepts samplePolicy ⟨["home", "other"], Mode.read⟩ = false := rfl
  rw [hfalse] at h2
  exact Bool.noConfusion h2

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

