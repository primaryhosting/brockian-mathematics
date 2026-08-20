/-!
# In Scope Encoding Sound
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA.Isolation

/-- Actions a proof-carrying app may request on a resource. -/
inductive Action where
  | read | write | exec
  deriving DecidableEq, Repr

/-- A resource path: a list of interned path segments. -/
abbrev Path := List Nat

/-- A capability: an action on a resource path. -/
structure Cap where
  action : Action
  path : Path
  deriving DecidableEq, Repr

/-- A scope of the isolation engine: prefix grants, together with deny rules
that override grants. -/
structure Scope where
  grants : List Cap
  denies : List Cap

/-- `Covers g c` : the rule `g` applies to the capability `c`, i.e. it concerns the
same action and its path is a prefix of (an ancestor of) the requested path. -/

def encodeCap (c : Cap) : Path := encAction c.action :: c.path

/-- The isolation engine's decision procedure, run entirely on encoded
capabilities: a request is allowed iff some encoded grant is a prefix of the
encoded request and no encoded deny rule is. -/
