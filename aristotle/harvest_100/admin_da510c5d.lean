/-!
# In Scope Encoding Complete
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_complete
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Isolation

/-- The kind of access a request asks for. -/
inductive Access
  | read
  | write
  deriving DecidableEq, Repr

/-- A request made by an application: a resource path together with an access mode. -/
structure Request where
  path : List String
  access : Access
  deriving DecidableEq, Repr

/-- A capability granted to an application: every resource under `prefixPath` may be read,
and may additionally be written when `mayWrite` is `true`. -/
structure Grant where
  prefixPath : List String
  mayWrite : Bool
  deriving DecidableEq, Repr

/-- Semantic ("model") notion of a grant permitting a request. -/
def Grant.Permits (g : Grant) (r : Request) : Prop :=
  g.prefixPath <+: r.path ∧ (r.access = Access.write → g.mayWrite = true)

/-- A request is in scope of a policy (a list of grants) when some grant permits it. -/
def InScope (gs : List Grant) (r : Request) : Prop :=
  ∃ g ∈ gs, g.Permits r

/-- Executable encoding of a single grant permitting a request, as used by the engine. -/
def Grant.encode (g : Grant) (r : Request) : Bool :=
  g.prefixPath.isPrefixOf r.path && (match r.access with
    | Access.read => true
    | Access.write => g.mayWrite)

/-- Executable encoding of the scope check performed by the isolation engine. -/
def encodeInScope (gs : List Grant) (r : Request) : Bool :=
  gs.any (fun g => g.encode r)

/-- A single grant's encoding is correct with respect to the semantic notion. -/
theorem grant_encode_iff (g : Grant) (r : Request) :
    g.encode r = true ↔ g.Permits r := by
  obtain ⟨p, a⟩ := r
  cases a <;>
    simp [Grant.encode, Grant.Permits, List.isPrefixOf_iff_prefix]

/-- **Completeness of the isolation engine's scope encoding**: every request that is in scope
according to the model is accepted by the executable encoding. -/
theorem in_scope_encoding_complete (gs : List Grant) (r : Request) :
    InScope gs r → encodeInScope gs r = true := by
  rintro ⟨g, hg, hperm⟩
  exact List.any_eq_true.2 ⟨g, hg, (grant_encode_iff g r).2 hperm⟩

/-- **Soundness of the isolation engine's scope encoding**: every request accepted by the
executable encoding really is in scope according to the model. -/
theorem in_scope_encoding_sound (gs : List Grant) (r : Request) :
    encodeInScope gs r = true → InScope gs r := by
  intro h
  obtain ⟨g, hg, hgr⟩ := List.any_eq_true.1 h
  exact ⟨g, hg, (grant_encode_iff g r).1 hgr⟩

/-- The encoding decides the scope relation exactly. -/
theorem in_scope_encoding_iff (gs : List Grant) (r : Request) :
    encodeInScope gs r = true ↔ InScope gs r :=
  ⟨in_scope_encoding_sound gs r, in_scope_encoding_complete gs r⟩

-- Sanity checks that the model is not degenerate.
example :
    encodeInScope [{ prefixPath := ["home", "app"], mayWrite := false }]
      { path := ["home", "app", "data"], access := Access.write } = false := by
  decide

example :
    encodeInScope [{ prefixPath := ["home", "app"], mayWrite := false }]
      { path := ["home", "app", "data"], access := Access.read } = true := by
  decide

example :
    encodeInScope [{ prefixPath := ["home", "app"], mayWrite := true }]
      { path := ["etc", "passwd"], access := Access.read } = false := by
  decide

#print axioms in_scope_encoding_complete

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

