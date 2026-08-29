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

theorem permits_iff_chain_subset (A : Allowlist) (p : Principal) :
    Permits A p ↔ ∀ q : Principal, InChain q p → A q := by
  induction p with
  | root n =>
      constructor
      · intro hp q hq; exact hq ▸ hp
      · intro h; exact h _ rfl
  | delegate q n ih =>
      constructor
      · intro h r hr
        cases hr with
        | inl heq => exact heq ▸ h.1
        | inr hr => exact (ih.mp h.2) r hr
      · intro h
        exact ⟨h _ (Or.inl rfl), ih.mpr fun r hr => h r (Or.inr hr)⟩

/-- Completeness of default deny for a delegation-closed allowlist: every
allowlisted principal is indeed permitted. -/
