/-
# Default Deny Excludes Only Allowlist
Category: Proof-Carrying Apps
Target: PCA.Invariant.default_deny_excludes_only_allowlist
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Default Deny Excludes Only Allowlist
Category: Proof-Carrying Apps
Target: PCA.Invariant.default_deny_excludes_only_allowlist
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA

/-- A request presented to the isolation engine: a subject asking to perform an
action on a resource. -/
structure Request (S A R : Type*) where
  subject : S
  action : A
  resource : R
  deriving DecidableEq

/-- A capability grant held by the isolation engine's allowlist. -/
structure Grant (S A R : Type*) where
  subject : S
  action : A
  resource : R
  deriving DecidableEq

/-- The decision returned by the isolation engine. -/
inductive Decision
  | allow
  | deny
  deriving DecidableEq, Repr

variable {S A R : Type*}

/-- A grant matches a request when subject, action and resource all agree. -/

theorem not_allowlisted_denied (caps : List (Grant S A R)) (r : Request S A R)
    (hr : r ∉ allowlist caps) : eval caps r = Decision.deny := by
  have h := default_deny_excludes_only_allowlist (caps := caps)
  have : r ∈ {r : Request S A R | eval caps r = Decision.deny} := by
    rw [h]; exact hr
  exact this

end Invariant

end Engine

end PCA

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

