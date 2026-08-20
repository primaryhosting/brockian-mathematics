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

theorem eval_eq_deny_iff_ne_allow (caps : List (Grant S A R)) (r : Request S A R) :
    eval caps r = Decision.deny ↔ eval caps r ≠ Decision.allow := by
  unfold eval
  split <;> simp

namespace Invariant

/-- **Default deny excludes only the allowlist.**

The set of requests denied by the isolation engine is *exactly* the complement of
the allowlist: the engine is sound (it never denies a request covered by a held
capability) and complete (it denies every request not covered by one). -/
