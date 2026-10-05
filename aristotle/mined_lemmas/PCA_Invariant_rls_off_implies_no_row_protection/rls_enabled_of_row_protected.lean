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

theorem rls_enabled_of_row_protected
    (t : Table Principal Row) {p : Principal} {r : Row} (h : RowProtected t p r) :
    t.rlsEnabled = true := by
  cases hb : t.rlsEnabled with
  | false => exact absurd h (rls_off_implies_no_row_protection t hb p r)
  | true => rfl

end PCA.Invariant

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

