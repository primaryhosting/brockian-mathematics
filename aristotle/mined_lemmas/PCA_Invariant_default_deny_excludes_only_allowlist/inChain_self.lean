/-!
# Default Deny Excludes Only Allowlist
Category: Proof-Carrying Apps
Target: PCA.Invariant.default_deny_excludes_only_allowlist
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA

/-- A principal of the isolation engine: either a root identity, or a principal
obtained by delegating from a parent principal under some capability name. -/
inductive Principal where
  | root : String → Principal
  | delegate : Principal → String → Principal
  deriving DecidableEq

namespace Principal

/-- `InChain q p` says that `q` occurs on the delegation chain of `p`, i.e. `q`
is `p` itself or one of its ancestors. -/

theorem inChain_self (p : Principal) : InChain p p := by
  cases p with
  | root n => rfl
  | delegate q n => exact Or.inl rfl

end Principal

namespace Invariant

open Principal

/-- An allowlist is a predicate on principals; the isolation engine's policy is
*default deny*, so anything not explicitly covered below is denied. -/
abbrev Allowlist := Principal → Prop

/-- The default-deny access decision: a principal is permitted only if it is
explicitly on the allowlist `A`, and (for a delegated principal) its parent is
permitted as well.  Every principal not covered by this rule is denied. -/
