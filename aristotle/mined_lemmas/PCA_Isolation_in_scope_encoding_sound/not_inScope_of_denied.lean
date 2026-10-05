/-!
# In Scope Encoding Sound
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA
namespace Isolation

/-- A resource is identified by a hierarchical path: a list of name segments,
read from the root downwards. -/
abbrev Path := List String

/-- The isolation policy of a sandboxed app: a list of granted subtrees
(`roots`) together with a list of explicitly revoked subtrees (`denied`). -/
structure Scope where
  /-- Subtrees the app has been granted access to. -/
  roots : List Path
  /-- Subtrees carved out of the grants; denial takes precedence. -/
  denied : List Path
  deriving Repr

/-- Declarative semantics of the isolation engine: a resource `p` lies in the
scope `s` when some granted root is an ancestor of (or equal to) `p`, and no
denied subtree is an ancestor of (or equal to) `p`. -/

theorem not_inScope_of_denied {s : Scope} {p : Path} {d : Path}
    (hd : d ∈ s.denied) (hdp : d <+: p) : ¬ InScope s p := by
  rintro ⟨-, h⟩
  exact h d hd hdp

/-- Scopes are closed downwards along the resource hierarchy in the following
sense: extending an in-scope path keeps it inside every granted root, so it can
only leave the scope by hitting an explicit denial. -/
