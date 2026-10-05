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
