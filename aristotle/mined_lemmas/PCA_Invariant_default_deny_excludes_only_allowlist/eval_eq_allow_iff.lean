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

theorem eval_eq_allow_iff (caps : List (Grant S A R)) (r : Request S A R) :
    eval caps r = Decision.allow ↔ r ∈ allowlist caps := by
  unfold eval allowlist
  by_cases h : caps.any (fun g => decide (g.Matches r))
  · simp only [h, if_pos, Set.mem_setOf_eq, true_iff]
    simpa using h
  · simp only [h, Set.mem_setOf_eq, if_false, reduceCtorEq, false_iff]
    simpa using h

/-- The engine returns `deny` exactly when it does not return `allow`. -/
