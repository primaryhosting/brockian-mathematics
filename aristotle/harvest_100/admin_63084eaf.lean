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
def inScope (s : Scope) (p : Path) : Prop := s.root <+: p

/-- Executable (engine-level) encoding of the in-scope check. -/
def encode (s : Scope) (p : Path) : Bool := s.root.isPrefixOf p

/-- **Soundness and completeness of the in-scope encoding**: the boolean check
performed by the isolation engine agrees exactly with the declarative model.

The proof is `List.isPrefixOf_iff_prefix` from the Lean core `List` API. -/
theorem in_scope_encoding_sound (s : Scope) (p : Path) :
    encode s p = true ↔ inScope s p :=
  List.isPrefixOf_iff_prefix

/-- Soundness direction: whatever the engine admits is genuinely in scope. -/
theorem in_scope_of_encode {s : Scope} {p : Path} (h : encode s p = true) : inScope s p :=
  (in_scope_encoding_sound s p).mp h

/-- Completeness direction: the engine admits everything in scope. -/
theorem encode_of_in_scope {s : Scope} {p : Path} (h : inScope s p) : encode s p = true :=
  (in_scope_encoding_sound s p).mpr h

/-- Negative form: refusal by the engine means genuinely out of scope. -/
theorem not_in_scope_of_encode_false {s : Scope} {p : Path} (h : encode s p = false) :
    ¬ inScope s p := by
  intro hp
  simp [encode_of_in_scope hp] at h

/-- The declarative model is decidable, with the engine's encoding as its decision procedure. -/
instance (s : Scope) : DecidablePred (inScope s) := fun p =>
  decidable_of_iff _ (in_scope_encoding_sound s p)

/-- An app's own root is always in its scope (reflexivity). -/
theorem inScope_root (s : Scope) : inScope s s.root := List.prefix_refl _

/-- Scopes are closed under extending a path downwards: isolation never leaks upwards. -/
theorem inScope_append {s : Scope} {p : Path} (h : inScope s p) (q : Path) :
    inScope s (p ++ q) := h.trans (List.prefix_append p q)

/-- Nested scopes: if `s₁`'s root is in scope for `s₂`, every `s₁`-resource is `s₂`-visible. -/
theorem inScope_trans {s₁ s₂ : Scope} {p : Path}
    (h : inScope s₂ s₁.root) (hp : inScope s₁ p) : inScope s₂ p :=
  h.trans hp

/-- A shared resource forces the two scope roots to be comparable: apps whose roots are
incomparable can never see the same resource. -/
theorem no_shared_resource {s₁ s₂ : Scope} {p : Path}
    (h₁ : inScope s₁ p) (h₂ : inScope s₂ p) :
    s₁.root <+: s₂.root ∨ s₂.root <+: s₁.root :=
  List.prefix_or_prefix_of_prefix h₁ h₂

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

