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

def InScope (s : Scope) (p : Path) : Prop :=
  (∃ r ∈ s.roots, r <+: p) ∧ ∀ d ∈ s.denied, ¬ d <+: p

/-- The executable encoding of the scope check used by the isolation engine. -/

def encodeInScope (s : Scope) (p : Path) : Bool :=
  s.roots.any (fun r => r.isPrefixOf p) && !s.denied.any (fun d => d.isPrefixOf p)

/-- **Soundness and completeness of the `in scope` encoding.**
The boolean decision procedure `encodeInScope` returns `true` on exactly those
resource paths that the declarative isolation model `InScope` admits. -/

theorem in_scope_encoding_sound (s : Scope) (p : Path) :
    encodeInScope s p = true ↔ InScope s p := by
  unfold encodeInScope InScope
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true,
    List.any_eq_false, List.isPrefixOf_iff_prefix]

/-- Decidability of the declarative model, transported along the encoding. -/
instance instDecidableInScope (s : Scope) (p : Path) : Decidable (InScope s p) :=
  decidable_of_iff _ (in_scope_encoding_sound s p)

/-- Denial always wins: a path lying under a denied subtree is never in scope. -/
