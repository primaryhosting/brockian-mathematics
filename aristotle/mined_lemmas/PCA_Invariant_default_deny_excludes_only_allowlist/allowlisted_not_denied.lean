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

theorem allowlisted_not_denied (caps : List (Grant S A R)) (r : Request S A R)
    (hr : r ∈ allowlist caps) : eval caps r ≠ Decision.deny := by
  have := default_deny_excludes_only_allowlist (caps := caps)
  intro hd
  have : r ∈ (allowlist caps)ᶜ := this ▸ hd
  exact this hr

/-- Completeness: everything off the allowlist is denied. -/
