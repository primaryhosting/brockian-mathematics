/-!
# In Scope Encoding Complete
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_complete
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The isolation model

An isolation engine mediates an application's access to resources.  A resource is
identified by a *path* (a list of path components), and an access is a *request*
consisting of a path together with the permission being exercised.

A *scope* grants a set of permissions on a whole subtree of the resource space,
namely on every path extending its `root`.  A *policy* is a list of scopes, and a
request is *in scope* for the policy when some scope of the policy grants it.

The engine does not evaluate policies directly: it first *encodes* a policy into a
normal form consisting of single-permission scopes, and then runs a purely Boolean
membership check against that encoding.  The results below say that this encoding is
faithful: it accepts every in-scope request (`in_scope_encoding_complete`) and only
in-scope requests (`in_scope_encoding_sound`).
-/

namespace PCA.Isolation

/-- A resource path: a list of path components. -/
abbrev Path := List String

/-- The permissions an isolation scope can grant. -/
inductive Perm
  | read
  | write
  | exec
  deriving DecidableEq, Repr

/-- An access request: a permission exercised on a resource path. -/
structure Request where
  path : Path
  perm : Perm
  deriving DecidableEq, Repr

/-- A scope grants the permissions in `perms` on every path extending `root`. -/
structure Scope where
  root : Path
  perms : List Perm
  deriving DecidableEq, Repr

/-- A policy is a list of scopes. -/
abbrev Policy := List Scope

/-- The scope `s` grants the request `r`: the scope root is a prefix of the requested
path and the exercised permission is granted. -/
def Scope.Grants (s : Scope) (r : Request) : Prop :=
  s.root <+: r.path ∧ r.perm ∈ s.perms

/-- The semantic notion the engine has to implement: some scope of the policy grants
the request. -/
def Policy.InScope (p : Policy) (r : Request) : Prop :=
  ∃ s ∈ p, s.Grants r

/-- The Boolean check the engine runs against a single (encoded) scope. -/
def Scope.check (s : Scope) (r : Request) : Bool :=
  s.root.isPrefixOf r.path && s.perms.contains r.perm

/-- The encoding of a policy: every scope is split into one single-permission scope
per granted permission (in particular, scopes granting nothing disappear). -/
def encode (p : Policy) : Policy :=
  p.flatMap fun s => s.perms.map fun q => { root := s.root, perms := [q] }

/-- The engine's decision procedure: run the Boolean check against the encoding. -/
def accepts (p : Policy) (r : Request) : Bool :=
  (encode p).any fun s => s.check r

/-- The Boolean scope check decides the semantic `Scope.Grants` relation. -/
theorem Scope.check_eq_true_iff (s : Scope) (r : Request) :
    s.check r = true ↔ s.Grants r := by
  simp [Scope.check, Scope.Grants, List.isPrefixOf_iff_prefix]

/-- Anything granted by a scope of the encoding is in scope for the original policy. -/
theorem grants_of_mem_encode {p : Policy} {r : Request} {t : Scope}
    (ht : t ∈ encode p) (h : t.Grants r) : p.InScope r := by
  simp only [encode, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨s, hs, q, hq, rfl⟩ := ht
  obtain ⟨hpre, hperm⟩ := h
  refine ⟨s, hs, hpre, ?_⟩
  simp only [List.mem_singleton] at hperm
  exact hperm ▸ hq

/-- **Completeness of the in-scope encoding.**  Whenever the policy semantically puts
a request in scope, the engine's encoded Boolean check accepts it. -/
theorem in_scope_encoding_complete (p : Policy) (r : Request) (h : p.InScope r) :
    accepts p r = true := by
  obtain ⟨s, hs, hpre, hperm⟩ := h
  have hmem : ({ root := s.root, perms := [r.perm] } : Scope) ∈ encode p := by
    simp only [encode, List.mem_flatMap, List.mem_map]
    exact ⟨s, hs, r.perm, hperm, rfl⟩
  refine List.any_eq_true.mpr ⟨_, hmem, ?_⟩
  exact (Scope.check_eq_true_iff _ r).mpr ⟨hpre, by simp⟩

/-- **Soundness of the in-scope encoding.**  The engine accepts only in-scope
requests. -/
theorem in_scope_encoding_sound (p : Policy) (r : Request) (h : accepts p r = true) :
    p.InScope r := by
  obtain ⟨t, ht, hchk⟩ := List.any_eq_true.mp h
  exact grants_of_mem_encode ht ((Scope.check_eq_true_iff t r).mp hchk)

/-- The engine's encoded Boolean check is exactly the semantic in-scope relation. -/
theorem accepts_eq_true_iff_inScope (p : Policy) (r : Request) :
    accepts p r = true ↔ p.InScope r :=
  ⟨in_scope_encoding_sound p r, in_scope_encoding_complete p r⟩

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

