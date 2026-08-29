/-!
# Rls Off Implies No Row Protection
Category: Proof-Carrying Apps
Target: PCA.Invariant.rls_off_implies_no_row_protection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA.Invariant

universe u v

/-- A row-level-security policy: it says which principals may see which rows. -/
structure Policy (P : Type u) (R : Type v) where
  /-- `permits p r` holds when the policy lets principal `p` observe row `r`. -/
  permits : P → R → Prop

/-- A table of the isolation engine's model: a row-level-security (RLS) switch
together with the list of policies attached to the table. -/
structure Table (P : Type u) (R : Type v) where
  /-- Whether row-level security is enabled on this table. -/
  rlsEnabled : Bool
  /-- The policies attached to the table. -/
  policies : List (Policy P R)

variable {P : Type u} {R : Type v}

/-- Semantics of the engine: when RLS is off every row is visible to every
principal; when RLS is on a row is visible only if some attached policy
permits it. -/

theorem rls_on_of_row_protection {t : Table P R} (h : t.RowProtection) :
    t.rlsEnabled = true := by
  rcases Bool.eq_false_or_eq_true t.rlsEnabled with hb | hb
  · exact hb
  · obtain ⟨p, r, hpr⟩ := h
    exact absurd (visible_of_rls_off hb p r) hpr

/-- **Main invariant.** If row-level security is switched off on a table, then
the table provides no row protection: no principal is denied any row. -/
