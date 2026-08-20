/-!
# In Scope Encoding Sound
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace PCA.Isolation

/-! ## The model of the isolation engine

A *proof-carrying app* runs inside an isolation engine.  Resources are named by
hierarchical paths (a list of path segments), and each access is tagged with a
capability (read / write / execute).  A *policy* is a finite list of grants; a
grant authorises a capability on every resource lying under a given path prefix.

`InScope` is the declarative (specification-level) notion of an access being
permitted.  `inScopeCheck` is the executable Boolean decision procedure that the
engine actually runs.  The target theorem states that the executable encoding is
both *sound* (it never accepts an access that the specification forbids) and
*complete* (it never rejects an access that the specification permits). -/

/-- A resource name: a hierarchical path, given as its list of segments. -/
abbrev Path := List String

/-- The capabilities an access can require. -/
inductive Cap
  | read
  | write
  | exec
  deriving DecidableEq, Repr

/-- A single grant in a policy: all capabilities in `caps` are authorised on
every resource whose path extends `root`. -/
structure Grant where
  root : Path
  caps : List Cap
  deriving DecidableEq, Repr

/-- A policy is a finite list of grants. -/
abbrev Policy := List Grant

/-- Specification: the access of capability `c` to resource `p` is in scope for
policy `P` when some grant of `P` both covers `p` (its root is a prefix of `p`)
and confers `c`. -/

theorem grantCovers_eq_true_iff (g : Grant) (c : Cap) (p : Path) :
    grantCovers g c p = true ↔ (g.root <+: p ∧ c ∈ g.caps) := by
  simp [grantCovers, List.isPrefixOf_iff_prefix]

/-- **Target.**  The executable in-scope encoding is sound and complete with
respect to the declarative isolation specification: the engine's Boolean check
accepts exactly the accesses that the policy authorises. -/
