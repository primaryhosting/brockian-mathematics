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

theorem deny_iff_not_allowlist (p : Policy) (q : Request) :
    p.eval q = Decision.deny ↔ ¬ p.Allowlist q := by
  rw [← allow_iff_allowlist]
  cases hq : p.eval q <;> simp

/-- Default deny: with no rules, every request is denied. -/
