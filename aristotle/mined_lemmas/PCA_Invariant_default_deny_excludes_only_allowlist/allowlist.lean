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

def allowlist (caps : List (Grant S A R)) : Set (Request S A R) :=
  {r | ∃ g ∈ caps, g.Matches r}

/-- The isolation engine's evaluation function.  It is *default deny*: the answer
is `allow` only when some held capability matches, and `deny` in every other
case. -/
