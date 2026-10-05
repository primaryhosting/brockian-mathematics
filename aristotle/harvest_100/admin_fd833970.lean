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
def permits (pol : Policy) (req : Request) : Bool :=
  pol.any fun g => decide (g.scope <+: req.path) && decide (req.op ∈ g.ops)

/-- A request is *in scope* for the policy when some grant covers it. -/
def InScope (pol : Policy) (req : Request) : Prop :=
  ∃ g ∈ pol, g.scope <+: req.path ∧ req.op ∈ g.ops

/-- The engine's decision procedure is exactly the `InScope` predicate. -/
theorem permits_iff_inScope (pol : Policy) (req : Request) :
    permits pol req = true ↔ InScope pol req := by
  simp [permits, InScope, List.any_eq_true]

/-- The isolated (sandbox-side) representation of a request: the capability it is
issued under, the path *relative* to that capability's scope, and the operation.
No absolute path is ever handed to the isolated component. -/
structure Encoded where
  grant : Grant
  rel : List String
  op : Op
  deriving DecidableEq, Repr

/-- The engine decodes an isolated representation back into an absolute request,
re-checking that the capability belongs to the policy and permits the operation. -/
def decode (pol : Policy) (e : Encoded) : Option Request :=
  if e.grant ∈ pol ∧ e.op ∈ e.grant.ops then
    some { path := e.grant.scope ++ e.rel, op := e.op }
  else
    none

/-- The encoder: pick the first grant of the policy covering the request, and
strip its scope off the request's path. -/
def encode (pol : Policy) (req : Request) : Option Encoded :=
  (pol.find? fun g => decide (g.scope <+: req.path) && decide (req.op ∈ g.ops)).map
    fun g => { grant := g, rel := req.path.drop g.scope.length, op := req.op }

/-- **Completeness of the in-scope encoding.**  Every request that the isolation
engine permits can be encoded, and the encoding decodes back to exactly that
request: no permitted access is lost by passing through the isolated
representation. -/
theorem in_scope_encoding_complete (pol : Policy) (req : Request)
    (h : permits pol req = true) :
    ∃ e : Encoded, encode pol req = some e ∧ decode pol e = some req := by
  classical
  set p : Grant → Bool :=
    fun g => decide (g.scope <+: req.path) && decide (req.op ∈ g.ops) with hp
  -- the search cannot fail, since `permits` found a covering grant
  have hne : pol.find? p ≠ none := by
    intro hnone
    rw [List.find?_eq_none] at hnone
    rw [permits_iff_inScope] at h
    obtain ⟨g, hg, hpre, hop⟩ := h
    have := hnone g hg
    simp [hp, hpre, hop] at this
  obtain ⟨g, hg⟩ := Option.ne_none_iff_exists'.1 hne
  have hgmem : g ∈ pol := List.mem_of_find?_eq_some hg
  have hgp : p g = true := List.find?_some hg
  have hpre : g.scope <+: req.path := by
    have h2 := hgp
    simp [hp] at h2
    exact h2.1
  have hop : req.op ∈ g.ops := by
    have h2 := hgp
    simp [hp] at h2
    exact h2.2
  refine ⟨{ grant := g, rel := req.path.drop g.scope.length, op := req.op }, ?_, ?_⟩
  · simp [encode, ← hp, hg]
  · have hcat : g.scope ++ req.path.drop g.scope.length = req.path := by
      obtain ⟨t, ht⟩ := hpre
      subst ht
      simp
    simp [decode, hgmem, hop, hcat]

/-- **Soundness of the isolation engine.**  Anything the engine decodes from an
isolated representation is itself a permitted request. -/
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

