/-!
# Default Deny Excludes Only Allowlist
Category: Proof-Carrying Apps
Target: PCA.Invariant.default_deny_excludes_only_allowlist
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA.Invariant

/-- Principals of the isolation engine: either a root principal, or a principal
obtained by delegation from a parent principal. -/
inductive Principal where
  | root (name : String)
  | delegate (parent : Principal) (name : String)
  deriving DecidableEq

/-- A policy assigns to each principal the allowlist of capabilities that this
principal explicitly grants, as a decidable predicate on capabilities. -/
abbrev Policy (Cap : Type) := Principal → Cap → Bool

variable {Cap : Type}

/-- The delegation chain of a principal: the principal itself together with all
of its ancestors. -/

theorem denied_eq_compl_effectiveAllow (pol : Policy Cap) (pr : Principal) :
    (fun c : Cap => granted pol pr c = false) = fun c : Cap => ¬ effectiveAllow pol pr c := by
  funext c
  exact propext (default_deny_excludes_only_allowlist pol pr c)

/-- Under the empty policy everything is denied: the engine really is default
deny. -/
