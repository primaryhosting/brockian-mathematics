/-!
# Default Deny Excludes Only Allowlist
Category: Proof-Carrying Apps
Target: PCA.Invariant.default_deny_excludes_only_allowlist
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA.Invariant

/-- Principals of the isolation engine: either a root principal, or a principal
obtained by delegation from a parent principal. -/
inductive Principal where
  | root (name : String)
  | delegate (parent : Principal) (name : String)
  deriving DecidableEq

/-- A policy assigns to each principal the allowlist of capabilities that this
principal explicitly grants, as a decidable predicate on capabilities. -/
abbrev Policy (Cap : Type) := Principal → Cap → Bool

variable {Cap : Type}

/-- The delegation chain of a principal: the principal itself together with all
of its ancestors. -/

theorem granted_delegate_le_parent (pol : Policy Cap) (p : Principal) (n : String) (c : Cap)
    (h : granted pol (.delegate p n) c = true) : granted pol p c = true := by
  simpa [granted] using ((Bool.and_eq_true _ _).mp h).2

end PCA.Invariant

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

