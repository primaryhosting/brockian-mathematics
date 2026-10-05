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

/-
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
Basic definitions for the Kahn–Kalai theorem (Park–Pham proof):
the Bernoulli product measure on subsets of a finite ground set, covers,
`p`-smallness, up-sets, and the parameters `q(F)`, `p_c(F)`, `ℓ(F)`.
-/

namespace Math2

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Bernoulli(`p`) product weight of a subset `A` inside the ground set `g`. -/

lemma w_sdiff_le {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) {p : ℝ} (hp0 : 0 ≤ p)
    {Z T : Finset α} (hTZ : T ⊆ Z) :
    w ρ (Z \ T) * p ^ T.card ≤ w ρ Z * (p / ρ) ^ T.card := by
  have hc : Z.card ≤ Fintype.card α := by
    simpa using Finset.card_le_card (Finset.subset_univ Z)
  have ht : T.card ≤ Z.card := Finset.card_le_card hTZ
  have hcard : (Z \ T).card = Z.card - T.card := Finset.card_sdiff_of_subset hTZ
  have hrho : (0:ℝ) ≤ 1 - ρ := by linarith
  have hpow : (1 - ρ) ^ (Fintype.card α - (Z.card - T.card)) ≤ (1 - ρ) ^ (Fintype.card α - Z.card) := by
    apply pow_le_pow_of_le_one hrho (by linarith)
    omega
  have hsplit : ρ ^ Z.card = ρ ^ (Z.card - T.card) * ρ ^ T.card := by
    rw [← pow_add]
    congr 1
    omega
  have hdiv : (p / ρ) ^ T.card = p ^ T.card / ρ ^ T.card := div_pow p ρ T.card
  rw [w, w, hcard, hdiv, hsplit]
  have hrpos : (0:ℝ) < ρ ^ T.card := pow_pos hρ0 _
  rw [div_eq_mul_inv]
  have key : ρ ^ (Z.card - T.card) * ρ ^ T.card * (1 - ρ) ^ (Fintype.card α - Z.card) *
      (p ^ T.card * (ρ ^ T.card)⁻¹)
      = ρ ^ (Z.card - T.card) * (1 - ρ) ^ (Fintype.card α - Z.card) * p ^ T.card := by
    field_simp
  rw [key]
  have hnn : (0:ℝ) ≤ ρ ^ (Z.card - T.card) * p ^ T.card :=
    mul_nonneg (pow_nonneg hρ0.le _) (pow_nonneg hp0 _)
  calc ρ ^ (Z.card - T.card) * (1 - ρ) ^ (Fintype.card α - (Z.card - T.card)) * p ^ T.card
      = ρ ^ (Z.card - T.card) * p ^ T.card * (1 - ρ) ^ (Fintype.card α - (Z.card - T.card)) := by
        ring
    _ ≤ ρ ^ (Z.card - T.card) * p ^ T.card * (1 - ρ) ^ (Fintype.card α - Z.card) :=
        mul_le_mul_of_nonneg_left hpow hnn
    _ = ρ ^ (Z.card - T.card) * (1 - ρ) ^ (Fintype.card α - Z.card) * p ^ T.card := by ring

