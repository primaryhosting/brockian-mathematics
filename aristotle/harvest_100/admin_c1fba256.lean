/-!
# Default Deny Excludes Only Allowlist
Category: Proof-Carrying Apps
Target: PCA.Invariant.default_deny_excludes_only_allowlist
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA
namespace Invariant

/-- Actions a subject may attempt on a resource. -/
inductive Action
  | read
  | write
  | exec
  deriving DecidableEq, Repr

/-- A capability request: a subject asking to perform an action on a resource. -/
structure Request where
  subject : String
  resource : String
  action : Action
  deriving DecidableEq, Repr

/-- An allowlist rule: either one exact request, or every action of a subject on a resource. -/
inductive Rule
  | exact (r : Request)
  | anyAction (subject resource : String)
  deriving DecidableEq, Repr

/-- Decidable test of whether a rule matches a request. -/
def Rule.Matches : Rule → Request → Bool
  | .exact r, q => decide (r = q)
  | .anyAction s res, q => decide (q.subject = s ∧ q.resource = res)

/-- A policy of the isolation engine is a finite list of allowlist rules. -/
structure Policy where
  rules : List Rule

/-- The allowlist of a policy: the requests some rule explicitly permits. -/
def Policy.Allowlist (p : Policy) (q : Request) : Prop :=
  ∃ rule ∈ p.rules, rule.Matches q = true

/-- The verdict returned by the isolation engine. -/
inductive Decision
  | allow
  | deny
  deriving DecidableEq, Repr

/-- The default-deny isolation engine: allow iff some allowlist rule matches, else deny. -/
def Policy.eval (p : Policy) (q : Request) : Decision :=
  if p.rules.any (fun rule => rule.Matches q) then Decision.allow else Decision.deny

/-- Soundness and completeness of `allow`: the engine allows exactly the allowlist. -/
theorem allow_iff_allowlist (p : Policy) (q : Request) :
    p.eval q = Decision.allow ↔ p.Allowlist q := by
  unfold Policy.eval Policy.Allowlist
  constructor
  · intro hh
    by_cases h : p.rules.any (fun rule => rule.Matches q) = true
    · exact List.any_eq_true.mp h
    · rw [if_neg h] at hh
      exact Decision.noConfusion hh
  · intro hh
    rw [if_pos (List.any_eq_true.mpr hh)]

/-- The engine denies exactly the requests outside the allowlist. -/
theorem deny_iff_not_allowlist (p : Policy) (q : Request) :
    p.eval q = Decision.deny ↔ ¬ p.Allowlist q := by
  rw [← allow_iff_allowlist]
  cases hq : p.eval q <;> simp

/-- Default deny: with no rules, every request is denied. -/
theorem eval_empty_deny (q : Request) : Policy.eval ⟨[]⟩ q = Decision.deny := by
  simp [Policy.eval]

/--
**Default deny excludes only the allowlist.**

The denied requests are precisely the complement of the allowlist, and the allowed requests are
precisely the allowlist. Hence the default-deny isolation engine is sound (it never allows
anything off the allowlist) and complete (it never excludes anything on the allowlist): the
exclusions of the engine are exactly the non-allowlisted requests, nothing more and nothing less.

Sets of requests are represented here as predicates `Request → Prop`, so the two set equalities
are stated as equalities of predicates.
-/
theorem default_deny_excludes_only_allowlist (p : Policy) :
    (fun q => p.eval q = Decision.deny) = (fun q => ¬ p.Allowlist q) ∧
      (fun q => p.eval q = Decision.allow) = p.Allowlist :=
  ⟨funext fun q => propext (deny_iff_not_allowlist p q),
   funext fun q => propext (allow_iff_allowlist p q)⟩

section Example

/-- A concrete policy: `alice` may do anything to `doc`; `bob` may only read `log`. -/
def samplePolicy : Policy :=
  { rules := [Rule.anyAction "alice" "doc",
              Rule.exact ⟨"bob", "log", Action.read⟩] }

example : samplePolicy.eval ⟨"alice", "doc", Action.write⟩ = Decision.allow := by decide

example : samplePolicy.eval ⟨"bob", "log", Action.read⟩ = Decision.allow := by decide

example : samplePolicy.eval ⟨"bob", "log", Action.write⟩ = Decision.deny := by decide

example : samplePolicy.eval ⟨"mallory", "doc", Action.read⟩ = Decision.deny := by decide

end Example

end Invariant
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

