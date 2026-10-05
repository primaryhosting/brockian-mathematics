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
