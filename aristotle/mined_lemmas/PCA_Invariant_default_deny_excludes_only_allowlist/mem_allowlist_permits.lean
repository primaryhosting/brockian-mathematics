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

theorem mem_allowlist_permits (A : Allowlist) (hA : DelegationClosed A) :
    ∀ p : Principal, A p → Permits A p := by
  intro p
  induction p with
  | root n => intro hp; exact hp
  | delegate q n ih => intro hp; exact ⟨hp, ih (hA q n hp)⟩

/-- **Default deny excludes only the allowlist.**  For a delegation-closed
allowlist `A`, the principals excluded (denied) by the default-deny engine are
exactly those that are not on the allowlist: no allowlisted principal is
excluded, and every non-allowlisted principal is. -/
