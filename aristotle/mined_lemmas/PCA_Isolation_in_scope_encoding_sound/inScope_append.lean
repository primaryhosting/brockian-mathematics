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

theorem inScope_append {s : Scope} {p q : Path} (hp : InScope s p)
    (hq : ∀ d ∈ s.denied, ¬ d <+: (p ++ q)) : InScope s (p ++ q) := by
  obtain ⟨⟨r, hr, hrp⟩, -⟩ := hp
  exact ⟨⟨r, hr, hrp.trans (List.prefix_append p q)⟩, hq⟩

/-- An empty grant list isolates the app completely. -/
