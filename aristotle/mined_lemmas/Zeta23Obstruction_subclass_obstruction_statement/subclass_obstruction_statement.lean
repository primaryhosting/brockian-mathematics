/-
# Subclass Obstruction Statement
Category: Brockian Conjecture
Target: Zeta23Obstruction.subclass_obstruction_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Subclass Obstruction Statement
Category: Brockian Conjecture
Target: Zeta23Obstruction.subclass_obstruction_statement
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

namespace Zeta23Obstruction

/-- A **configuration** of deep points: finitely many species, each carrying a real
"deep point" `pt i` and a strictly positive weight `wt i`. -/
structure DeepConfig where
  /-- number of species -/
  n : ℕ
  /-- the deep point attached to each species -/
  pt : Fin n → ℝ
  /-- the (strictly positive) weight attached to each species -/
  wt : Fin n → ℝ
  /-- positivity of the weights -/
  wt_pos : ∀ i : Fin n, 0 < wt i

/-- The **linear charge** of a configuration relative to a fixed kernel `R`:
the linear functional `c ↦ ∑ᵢ wᵢ · R(zᵢ)` obtained by per-species linear charging. -/

theorem subclass_obstruction_statement
    (R σ : ℝ → ℝ) (hRσ : ∀ x : ℝ, R (σ x) = R x)
    (z : ℝ) (hz : R z < 0) :
    (∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b),
        ¬ TermwiseNonneg R (deepPair σ z a b ha hb) ∧
          charge R (deepPair σ z a b ha hb) < 0) ∧
      ¬ CertificateValid R σ := by
  have key : ∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b),
      ¬ TermwiseNonneg R (deepPair σ z a b ha hb) ∧
        charge R (deepPair σ z a b ha hb) < 0 := by
    intro a b ha hb
    have hcharge : charge R (deepPair σ z a b ha hb) = a * R z + b * R z := by
      simp [charge, deepPair, Fin.sum_univ_two, hRσ]
    constructor
    · intro h
      have h0 := h ⟨0, by norm_num [deepPair]⟩
      simp [deepPair] at h0
      nlinarith
    · rw [hcharge]
      nlinarith
  refine ⟨key, ?_⟩
  intro hvalid
  exact (key 1 1 one_pos one_pos).1 (hvalid z 1 1 one_pos one_pos)

/-- Strengthening: the obstruction is not special to the two-species pair.  *Any*
configuration that charges some species at a point where the fixed kernel is negative
already breaks the termwise bound, whatever the (positive) weights are. -/
