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

