/-
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace CS

/-- A finite constraint satisfaction problem (CSP) instance: `numVars` variables taking
values in an alphabet of size `alphabetSize`, together with a nonempty list of Boolean
constraints on assignments. -/
structure CSP where
  numVars : ℕ
  alphabetSize : ℕ
  alphabet_pos : 0 < alphabetSize
  constraints : List ((Fin numVars → Fin alphabetSize) → Bool)
  constraints_ne : constraints ≠ []

namespace CSP

/-- Assignments of the CSP `G`. -/

theorem unsat_eq_zero_iff (G : CSP) : G.unsat = 0 ↔ G.Satisfiable := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := G.exists_unsat_eq
    refine ⟨a, ?_⟩
    rw [← G.numFalsified_eq_zero_iff a]
    have hs : (0 : ℝ) < G.size := by exact_mod_cast G.size_pos
    have hz : ((G.numFalsified a : ℝ)) / G.size = 0 := by rw [← ha, h]
    have := (div_eq_zero_iff.mp hz).resolve_right hs.ne'
    exact_mod_cast this
  · rintro ⟨a, ha⟩
    have h0 : G.numFalsified a = 0 := (G.numFalsified_eq_zero_iff a).mpr ha
    have hle : G.unsat ≤ 0 := by
      have := G.unsat_le a
      rwa [h0, Nat.cast_zero, zero_div] at this
    exact le_antisymm hle G.unsat_nonneg

/-- An unsatisfiable CSP violates at least one out of `size` constraints, so its unsat value
is at least `1 / size`. -/
