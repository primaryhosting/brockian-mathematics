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

def Grant.Matches (g : Grant S A R) (r : Request S A R) : Prop :=
  g.subject = r.subject ∧ g.action = r.action ∧ g.resource = r.resource

instance [DecidableEq S] [DecidableEq A] [DecidableEq R]
    (g : Grant S A R) (r : Request S A R) : Decidable (g.Matches r) := by
  unfold Grant.Matches; infer_instance

/-- The allowlist induced by a list of capability grants: exactly those requests
covered by some grant. -/
