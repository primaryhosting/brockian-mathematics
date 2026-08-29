/-!
# Rls Off Implies No Row Protection
Category: Proof-Carrying Apps
Target: PCA.Invariant.rls_off_implies_no_row_protection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Invariant

universe u v

/-- A row-level security policy for a table: it names, for each principal,
the set of rows that principal is permitted to see. -/
structure Policy (Principal : Type u) (Row : Type v) where
  /-- `permits p r` holds when this policy lets principal `p` see row `r`. -/
  permits : Principal → Row → Prop

/-- A table of the isolation engine's model: a row-level-security switch
together with the list of policies attached to the table. -/
structure Table (Principal : Type u) (Row : Type v) where
  /-- Whether row-level security is switched on for this table. -/
  rlsEnabled : Bool
  /-- The row-level security policies attached to the table. -/
  policies : List (Policy Principal Row)

variable {Principal : Type u} {Row : Type v}

/-- Semantics of the engine: when row-level security is off the table is read
wholesale, so every row is visible to every principal; when it is on a row is
visible only if some attached policy permits it. -/

def RowProtected (t : Table Principal Row) (p : Principal) (r : Row) : Prop :=
  ¬ Visible t p r

/-- **Soundness of the isolation model.** If row-level security is switched off
for a table, then no row of that table is protected from any principal. -/
