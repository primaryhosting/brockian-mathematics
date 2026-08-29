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

theorem rowProtection_iff (t : Table P R) :
    t.RowProtection ↔
      t.rlsEnabled = true ∧ ∃ (p : P) (r : R), ∀ pol ∈ t.policies, ¬ pol.permits p r := by
  constructor
  · intro h
    refine ⟨rls_on_of_row_protection h, ?_⟩
    obtain ⟨p, r, hpr⟩ := h
    refine ⟨p, r, fun pol hpol hperm => hpr ?_⟩
    intro _
    exact ⟨pol, hpol, hperm⟩
  · rintro ⟨hOn, p, r, hno⟩
    refine ⟨p, r, fun hvis => ?_⟩
    obtain ⟨pol, hpol, hperm⟩ := hvis hOn
    exact hno pol hpol hperm

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

