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

theorem encode_of_in_scope {s : Scope} {p : Path} (h : inScope s p) : encode s p = true :=
  (in_scope_encoding_sound s p).mpr h

/-- Negative form: refusal by the engine means genuinely out of scope. -/
