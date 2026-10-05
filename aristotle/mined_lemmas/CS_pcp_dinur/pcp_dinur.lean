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

theorem pcp_dinur (amp : CSP → CSP) (C : ℕ) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hsize : ∀ G : CSP, (amp G).size ≤ C * G.size)
    (hcomp : ∀ G : CSP, G.Satisfiable → (amp G).Satisfiable)
    (hgap : ∀ G : CSP, min α (2 * G.unsat) ≤ (amp G).unsat)
    (G : CSP) :
    (amp^[Nat.log 2 G.size + 1] G).size ≤ C ^ (Nat.log 2 G.size + 1) * G.size ∧
    (G.Satisfiable → (amp^[Nat.log 2 G.size + 1] G).Satisfiable) ∧
    (¬ G.Satisfiable → α ≤ (amp^[Nat.log 2 G.size + 1] G).unsat) := by
  refine ⟨size_iterate_le hsize G _, fun h => satisfiable_iterate hcomp G _ h, fun h => ?_⟩
  set t := Nat.log 2 G.size + 1 with ht
  have hs : (0 : ℝ) < G.size := by exact_mod_cast G.size_pos
  have hu : (1 : ℝ) / G.size ≤ G.unsat := G.inv_size_le_unsat h
  have hlt : G.size < 2 ^ t := Nat.lt_pow_succ_log_self (by norm_num) G.size
  have hltR : (G.size : ℝ) ≤ (2 : ℝ) ^ t := by
    have : ((G.size : ℝ)) ≤ ((2 ^ t : ℕ) : ℝ) := by exact_mod_cast hlt.le
    simpa using this
  have hone : (1 : ℝ) ≤ 2 ^ t * G.unsat := by
    have h1 : (2 : ℝ) ^ t * (1 / G.size) ≤ 2 ^ t * G.unsat := by
      have : (0 : ℝ) < 2 ^ t := by positivity
      exact mul_le_mul_of_nonneg_left hu this.le
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ t * (1 / G.size) := by
      rw [mul_one_div, le_div_iff₀ hs, one_mul]
      exact hltR
    linarith
  have hmin : min α ((2 : ℝ) ^ t * G.unsat) = α := min_eq_left (by linarith)
  have := gap_iterate hα0 hgap G t
  rwa [hmin] at this

end CS

