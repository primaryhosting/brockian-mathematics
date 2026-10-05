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

/-!
# Default Deny Excludes Only Allowlist
Category: Proof-Carrying Apps
Target: PCA.Invariant.default_deny_excludes_only_allowlist
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA.Invariant

universe u

/-- The two possible outcomes of a policy evaluation performed by the isolation engine. -/
inductive Decision
  | allow
  | deny
  deriving DecidableEq, Repr

/-- An access request: a principal performing an action on a resource. -/
structure Request (P A R : Type u) where
  principal : P
  action : A
  resource : R

/-- A matching pattern used inside an allow-rule: either a wildcard, or an exact value. -/
inductive Pattern (α : Type u)
  | any
  | exact (a : α)

namespace Pattern

variable {α : Type u}

/-- Declarative (propositional) semantics of pattern matching. -/
def Matches : Pattern α → α → Prop
  | .any, _ => True
  | .exact a, b => a = b

/-- Executable (boolean) pattern matching. -/
def matchesB [DecidableEq α] : Pattern α → α → Bool
  | .any, _ => true
  | .exact a, b => a == b

/-- The executable matcher agrees with the declarative semantics. -/
@[simp]
theorem matchesB_eq_true_iff [DecidableEq α] (p : Pattern α) (x : α) :
    p.matchesB x = true ↔ p.Matches x := by
  cases p with
  | any => simp [matchesB, Matches]
  | «exact» a => simp [matchesB, Matches]

end Pattern

variable {P A R : Type u}

/-- An allow-rule of the isolation engine: one pattern for each field of a request. -/
structure Rule (P A R : Type u) where
  principal : Pattern P
  action : Pattern A
  resource : Pattern R

namespace Rule

/-- A rule matches a request when all three of its patterns match. -/
def Matches (rule : Rule P A R) (req : Request P A R) : Prop :=
  rule.principal.Matches req.principal ∧
  rule.action.Matches req.action ∧
  rule.resource.Matches req.resource

/-- Executable (boolean) rule matching. -/
def matchesB [DecidableEq P] [DecidableEq A] [DecidableEq R]
    (rule : Rule P A R) (req : Request P A R) : Bool :=
  rule.principal.matchesB req.principal &&
  rule.action.matchesB req.action &&
  rule.resource.matchesB req.resource

/-- The executable rule matcher agrees with the declarative semantics. -/
@[simp]
theorem matchesB_eq_true_iff [DecidableEq P] [DecidableEq A] [DecidableEq R]
    (rule : Rule P A R) (req : Request P A R) :
    rule.matchesB req = true ↔ rule.Matches req := by
  simp [matchesB, Matches, and_assoc]

end Rule

/-- A policy is a finite list of allow-rules.  Anything not matched is denied by default. -/
structure Policy (P A R : Type u) where
  rules : List (Rule P A R)

namespace Policy

/-- Membership in the allowlist of a policy: some rule of the policy matches the request. -/
def Allowlisted (pol : Policy P A R) (req : Request P A R) : Prop :=
  ∃ rule ∈ pol.rules, rule.Matches req

/-- The default-deny evaluation function of the isolation engine: a request is allowed
iff some allow-rule matches it, and denied otherwise. -/
def evaluate [DecidableEq P] [DecidableEq A] [DecidableEq R]
    (pol : Policy P A R) (req : Request P A R) : Decision :=
  if pol.rules.any (fun rule => rule.matchesB req) then Decision.allow else Decision.deny

variable [DecidableEq P] [DecidableEq A] [DecidableEq R]

/-- The boolean scan over the rule list decides allowlist membership. -/
theorem any_matchesB_eq_true_iff (pol : Policy P A R) (req : Request P A R) :
    (pol.rules.any (fun rule => rule.matchesB req)) = true ↔ pol.Allowlisted req := by
  simp [Allowlisted, List.any_eq_true]

/-- Soundness: the engine allows a request exactly when the request is allowlisted. -/
theorem evaluate_eq_allow_iff (pol : Policy P A R) (req : Request P A R) :
    pol.evaluate req = Decision.allow ↔ pol.Allowlisted req := by
  rw [evaluate, ← any_matchesB_eq_true_iff]
  cases h : pol.rules.any (fun rule => rule.matchesB req) with
  | false => simp
  | true => simp

/-- Completeness of default deny: the engine denies a request exactly when it is
not allowlisted. -/
theorem evaluate_eq_deny_iff (pol : Policy P A R) (req : Request P A R) :
    pol.evaluate req = Decision.deny ↔ ¬ pol.Allowlisted req := by
  rw [evaluate, ← any_matchesB_eq_true_iff]
  cases h : pol.rules.any (fun rule => rule.matchesB req) with
  | false => simp
  | true => simp

end Policy

/-- **Default deny excludes only the allowlist.**

The isolation engine evaluates every request against a finite list of allow-rules and denies
anything that no rule matches.  The requests it denies are *exactly* those outside the policy's
allowlist: no allowlisted request is denied (soundness), and every non-allowlisted request is
denied (default deny). -/
theorem default_deny_excludes_only_allowlist
    {P A R : Type u} [DecidableEq P] [DecidableEq A] [DecidableEq R]
    (pol : Policy P A R) (req : Request P A R) :
    pol.evaluate req = Decision.deny ↔ ¬ pol.Allowlisted req :=
  pol.evaluate_eq_deny_iff req

end PCA.Invariant

import Mathlib
import RequestProject.PCA.Invariant

/-!
# Set-theoretic form of the default-deny invariant

Restatement of `PCA.Invariant.default_deny_excludes_only_allowlist` using Mathlib's `Set`
machinery: the set of denied requests is literally the complement of the allowlist.
-/

set_option autoImplicit false

namespace PCA.Invariant

universe u

namespace Policy

variable {P A R : Type u} [DecidableEq P] [DecidableEq A] [DecidableEq R]

/-- The allowlist of a policy, as a set of requests. -/
def allowlist (pol : Policy P A R) : Set (Request P A R) :=
  {req | pol.Allowlisted req}

/-- The set of requests denied by the isolation engine is exactly the complement of the
policy's allowlist. -/
theorem denySet_eq_compl_allowlist (pol : Policy P A R) :
    {req : Request P A R | pol.evaluate req = Decision.deny} = (pol.allowlist)ᶜ := by
  ext req
  simpa [allowlist] using pol.evaluate_eq_deny_iff req

end Policy

end PCA.Invariant

