/-
# Rls Off Implies No Row Protection
Category: Proof-Carrying Apps
Target: PCA.Invariant.rls_off_implies_no_row_protection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace PCA

/-- A row-level security policy: it says which principals are permitted to see which rows. -/
structure Policy (Principal Row : Type*) where
  /-- `permits p r` holds when the policy grants principal `p` access to row `r`. -/
  permits : Principal → Row → Prop

/-- A table of the isolation engine's model: a row-level-security (RLS) switch together with
the list of policies that are consulted when the switch is on. -/
structure Table (Principal Row : Type*) where
  /-- Whether row-level security is enabled for this table. -/
  rlsEnabled : Bool
  /-- The policies attached to the table (only consulted when `rlsEnabled = true`). -/
  policies : List (Policy Principal Row)

variable {Principal Row : Type*}

/-- Access semantics of the engine: when RLS is off every row is visible to every principal;
when RLS is on a row is visible only if some attached policy permits it. -/

theorem visible_of_rls_off
    (t : Table Principal Row) (h : t.rlsEnabled = false) (p : Principal) (r : Row) :
    t.Visible p r :=
  Or.inl h

/-- Converse (completeness of the invariant): if some row is protected, RLS must be on. -/
