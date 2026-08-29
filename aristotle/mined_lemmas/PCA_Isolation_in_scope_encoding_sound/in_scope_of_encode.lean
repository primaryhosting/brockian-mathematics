/-!
# In Scope Encoding Sound
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA.Isolation

/-- A resource is addressed by a hierarchical path (e.g. `["app", "data", "db"]`). -/
abbrev Path := List String

/-- An isolation scope granted to an app: everything below `root` is reachable. -/
structure Scope where
  root : Path
deriving DecidableEq

/-- Declarative (specification-level) model: `p` is in scope for `s` iff the scope
root is a prefix of `p`, i.e. `p` lies in the subtree rooted at `s.root`. -/

theorem in_scope_of_encode {s : Scope} {p : Path} (h : encode s p = true) : inScope s p :=
  (in_scope_encoding_sound s p).mp h

/-- Completeness direction: the engine admits everything in scope. -/
