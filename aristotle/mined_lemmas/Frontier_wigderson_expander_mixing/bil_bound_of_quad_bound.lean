/-
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
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

namespace Frontier

section Mixing

variable {n : ℕ}

/-- The bilinear form `xᵀ A y` associated with a real matrix `A`. -/

lemma bil_bound_of_quad_bound {A : Matrix (Fin n) (Fin n) ℝ} (hsymm : A.IsSymm) {lam : ℝ}
    (hlam : ∀ x : Fin n → ℝ, (∑ i, x i) = 0 → |bil A x x| ≤ lam * nsq x)
    (x y : Fin n → ℝ) (hx : ∑ i, x i = 0) (hy : ∑ i, y i = 0) :
    |bil A x y| ≤ lam * Real.sqrt (nsq x) * Real.sqrt (nsq y) := by
  rcases eq_or_lt_of_le (nsq_nonneg x) with hx0 | hxpos
  · have hz : ∀ i, x i = 0 := (nsq_eq_zero_iff x).1 hx0.symm
    have hb : bil A x y = 0 := by
      unfold bil
      exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by rw [hz i]; ring
    rw [hb, ← hx0]
    simp
  rcases eq_or_lt_of_le (nsq_nonneg y) with hy0 | hypos
  · have hz : ∀ i, y i = 0 := (nsq_eq_zero_iff y).1 hy0.symm
    have hb : bil A x y = 0 := by
      unfold bil
      exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by rw [hz j]; ring
    rw [hb, ← hy0]
    simp
  set p := Real.sqrt (nsq x) with hp
  set q := Real.sqrt (nsq y) with hq
  have hppos : 0 < p := Real.sqrt_pos.2 hxpos
  have hqpos : 0 < q := Real.sqrt_pos.2 hypos
  have hp2 : p ^ 2 = nsq x := Real.sq_sqrt hxpos.le
  have hq2 : q ^ 2 = nsq y := Real.sq_sqrt hypos.le
  set u : Fin n → ℝ := fun i => p⁻¹ * x i with hu
  set v : Fin n → ℝ := fun i => q⁻¹ * y i with hv
  have hsu : ∑ i, u i = 0 := by
    rw [hu, ← Finset.mul_sum, hx, mul_zero]
  have hsv : ∑ i, v i = 0 := by
    rw [hv, ← Finset.mul_sum, hy, mul_zero]
  have hnu : nsq u = 1 := by
    have h3 : nsq u = p⁻¹ ^ 2 * nsq x := by
      unfold nsq
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hu]; ring
    rw [h3, ← hp2]
    field_simp
  have hnv : nsq v = 1 := by
    have h3 : nsq v = q⁻¹ ^ 2 * nsq y := by
      unfold nsq
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hv]; ring
    rw [h3, ← hq2]
    field_simp
  have hbuv : bil A u v = (p * q)⁻¹ * bil A x y := by
    rw [hu, hv, bil_smul_left, bil_smul_right]
    field_simp
  have hsadd : ∑ i, (u i + v i) = 0 := by
    rw [Finset.sum_add_distrib, hsu, hsv]; ring
  have hssub : ∑ i, (u i - v i) = 0 := by
    rw [Finset.sum_sub_distrib, hsu, hsv]; ring
  have h1 := hlam (fun i => u i + v i) hsadd
  have h2 := hlam (fun i => u i - v i) hssub
  have hpol := bil_polarization hsymm u v
  have hkey : 4 * |bil A u v| ≤ lam * (nsq (fun i => u i + v i) + nsq (fun i => u i - v i)) := by
    have h4 : |4 * bil A u v| ≤ lam * nsq (fun i => u i + v i) + lam * nsq (fun i => u i - v i) := by
      rw [hpol]
      calc |bil A (fun i => u i + v i) (fun i => u i + v i)
              - bil A (fun i => u i - v i) (fun i => u i - v i)|
          ≤ |bil A (fun i => u i + v i) (fun i => u i + v i)|
              + |bil A (fun i => u i - v i) (fun i => u i - v i)| := abs_sub _ _
        _ ≤ lam * nsq (fun i => u i + v i) + lam * nsq (fun i => u i - v i) :=
            add_le_add h1 h2
    rw [abs_mul] at h4
    simp only [Nat.abs_ofNat] at h4
    linarith [h4]
  rw [nsq_add_sub, hnu, hnv] at hkey
  have hlam_nonneg : 0 ≤ lam := by nlinarith [abs_nonneg (bil A u v)]
  have hle : |bil A u v| ≤ lam := by linarith
  rw [hbuv, abs_mul] at hle
  have habs : |(p * q)⁻¹| = (p * q)⁻¹ := abs_of_pos (by positivity)
  rw [habs] at hle
  have hpq : (0:ℝ) < p * q := by positivity
  have hmul : |bil A x y| ≤ lam * (p * q) := by
    calc |bil A x y| = (p * q) * ((p * q)⁻¹ * |bil A x y|) := by field_simp
      _ ≤ (p * q) * lam := mul_le_mul_of_nonneg_left hle hpq.le
      _ = lam * (p * q) := by ring
  linarith [hmul]

/-- Shifting both arguments of the bilinear form by constants. -/
