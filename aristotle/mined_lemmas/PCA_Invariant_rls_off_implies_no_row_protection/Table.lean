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

def Table.RowProtection (t : Table P R) : Prop :=
  ∃ (p : P) (r : R), ¬ t.Visible p r

/-- With RLS off, every row is visible to every principal. -/
