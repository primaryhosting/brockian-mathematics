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

def Policy.InScope (p : Policy) (r : Request) : Prop :=
  ∃ s ∈ p, s.Grants r

/-- The Boolean check the engine runs against a single (encoded) scope. -/
