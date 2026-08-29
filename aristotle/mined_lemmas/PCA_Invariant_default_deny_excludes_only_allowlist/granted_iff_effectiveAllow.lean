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

theorem granted_iff_effectiveAllow (pol : Policy Cap) (pr : Principal) (c : Cap) :
    granted pol pr c = true ↔ effectiveAllow pol pr c := by
  induction pr with
  | root n => simp [granted, effectiveAllow, chain]
  | delegate p n ih =>
      simp only [granted, effectiveAllow, chain, Bool.and_eq_true, List.mem_cons,
        forall_eq_or_imp] at *
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, ih.mp h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, ih.mpr h2⟩

/-- **Default deny excludes only the allowlist.**  A request is denied by the
isolation engine exactly when the requested capability is *not* in the effective
allowlist of the requesting principal: nothing on the allowlist is ever denied,
and everything off it is denied. -/
