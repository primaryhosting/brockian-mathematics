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

theorem amplification_hypotheses_consistent :
    ∃ (amp : CSP → CSP) (C : ℕ) (α : ℝ), 0 < α ∧ α ≤ 1 ∧
      (∀ G : CSP, (amp G).size ≤ C * G.size) ∧
      (∀ G : CSP, G.Satisfiable → (amp G).Satisfiable) ∧
      (∀ G : CSP, min α (2 * G.unsat) ≤ (amp G).unsat) := by
  refine ⟨fun G => if G.Satisfiable then trivSat else trivUnsat, 1, 1, one_pos, le_rfl,
    ?_, ?_, ?_⟩
  · intro G
    have h := G.size_pos
    by_cases hG : G.Satisfiable <;> simp [hG, trivSat_size, trivUnsat_size] <;> omega
  · intro G hG
    simpa [hG] using trivSat_satisfiable
  · intro G
    by_cases hG : G.Satisfiable
    · have h0 : G.unsat = 0 := (CSP.unsat_eq_zero_iff _).mpr hG
      simp [hG, h0, trivSat_unsat]
    · simp only [hG, if_false, trivUnsat_unsat]
      exact min_le_left _ _

variable {amp : CSP → CSP}

/-- Iterating a size-`C`-blow-up transformation `t` times blows the size up by at most `C ^ t`. -/
