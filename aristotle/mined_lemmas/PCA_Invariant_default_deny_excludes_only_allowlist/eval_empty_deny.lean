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
