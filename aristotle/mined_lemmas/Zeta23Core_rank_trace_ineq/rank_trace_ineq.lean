/-
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped ComplexOrder

open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Basic notions -/

/-- The real part of the trace of a matrix. -/

theorem rank_trace_ineq {P Q : Matrix n n 𝕜} (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b) {c : ℝ} (hc : 0 < c) :
    c * rtr P - c ^ 2 / 4 * r + 2 * c * rtr Q - c ^ 2 * b ≤ froSq (P + Q) := by
  obtain ⟨E, hE, hE2, hEtr, hEneg⟩ := exists_spectral_proj hQ
  have hF : (1 - E : Matrix n n 𝕜).IsHermitian := proj_compl_herm hE
  have hF2 : (1 - E) * (1 - E) = (1 : Matrix n n 𝕜) - E := proj_compl_sq hE2
  have hS : (P + Q).IsHermitian := hP.isHermitian.add hQ
  -- the compression `R` of `P` to the complement of `E`
  have hRpsd : ((1 - E) * P * (1 - E)).PosSemidef := by
    have h := hP.mul_mul_conjTranspose_same (1 - E)
    rwa [hF.eq] at h
  obtain ⟨G, hG, hG2, hGtr, hGneg⟩ := exists_spectral_proj hRpsd.isHermitian
  -- splitting the Frobenius norm into the four blocks
  have hsplit : froSq (P + Q)
      = (froSq (E * (P + Q) * E) + froSq (E * (P + Q) * (1 - E)))
        + (froSq ((1 - E) * (P + Q) * E) + froSq ((1 - E) * (P + Q) * (1 - E))) := by
    rw [froSq_split_left hE hE2 (P + Q), froSq_split_right hE hE2 (E * (P + Q)),
      froSq_split_right hE hE2 ((1 - E) * (P + Q))]
  have hge : froSq (E * (P + Q) * E) + froSq ((1 - E) * (P + Q) * (1 - E)) ≤ froSq (P + Q) := by
    rw [hsplit]
    have h1 := froSq_nonneg (E * (P + Q) * (1 - E))
    have h2 := froSq_nonneg ((1 - E) * (P + Q) * E)
    linarith
  -- bound on the `E`-block
  have hEcompl : (1 - E) * E = (0 : Matrix n n 𝕜) := by
    rw [Matrix.sub_mul, hE2, Matrix.one_mul, sub_self]
  have hAneg : rtr ((1 - E) * (E * (P + Q) * E) * (1 - E)) ≤ 0 := by
    have hz : (1 - E) * (E * (P + Q) * E) * (1 - E) = 0 := by
      rw [show (1 - E) * (E * (P + Q) * E) = ((1 - E) * E) * ((P + Q) * E) by
        simp [Matrix.mul_assoc], hEcompl]
      simp
    rw [hz]
    simp [rtr]
  have hbA := quad_bound (conj_herm hE hS) hE hE2 hc hAneg
  -- bound on the complementary block
  have hBsplit : (1 - E) * (P + Q) * (1 - E)
      = (1 - E) * P * (1 - E) + (1 - E) * Q * (1 - E) := by
    rw [Matrix.mul_add, Matrix.add_mul]
  have hBneg : rtr ((1 - G) * ((1 - E) * (P + Q) * (1 - E)) * (1 - G)) ≤ 0 := by
    have hexp : (1 - G) * ((1 - E) * (P + Q) * (1 - E)) * (1 - G)
        = (1 - G) * ((1 - E) * P * (1 - E)) * (1 - G)
          + (1 - G) * ((1 - E) * Q * (1 - E)) * (1 - G) := by
      rw [hBsplit, Matrix.mul_add, Matrix.add_mul]
    have t1 : rtr ((1 - G) * ((1 - E) * P * (1 - E)) * (1 - G)) ≤ 0 :=
      rtr_nonpos_of_neg_posSemidef hGneg
    have t2 : rtr ((1 - G) * ((1 - E) * Q * (1 - E)) * (1 - G)) ≤ 0 := by
      refine rtr_nonpos_of_neg_posSemidef ?_
      have hrw : -((1 - G) * ((1 - E) * Q * (1 - E)) * (1 - G))
          = (1 - G) * (-((1 - E) * Q * (1 - E))) * (1 - G)ᴴ := by
        rw [(proj_compl_herm hG).eq]
        simp
      rw [hrw]
      exact hEneg.mul_mul_conjTranspose_same _
    rw [hexp, rtr_add]
    linarith
  have hbB := quad_bound (conj_herm hF hS) hG hG2 (by positivity : (0:ℝ) < c / 2) hBneg
  -- trace bookkeeping
  have hPsplit : rtr (E * P * E) + rtr ((1 - E) * P * (1 - E)) = rtr P := rtr_proj_split hE2 P
  have hQsplit : rtr (E * Q * E) + rtr ((1 - E) * Q * (1 - E)) = rtr Q := rtr_proj_split hE2 Q
  have hAtr : rtr (E * (P + Q) * E) = rtr (E * P * E) + rtr (E * Q * E) := by
    rw [show E * (P + Q) * E = E * P * E + E * Q * E by rw [Matrix.mul_add, Matrix.add_mul],
      rtr_add]
  have hBtr : rtr ((1 - E) * (P + Q) * (1 - E))
      = rtr ((1 - E) * P * (1 - E)) + rtr ((1 - E) * Q * (1 - E)) := by
    rw [hBsplit, rtr_add]
  have ha : 0 ≤ rtr (E * P * E) := by
    refine rtr_nonneg ?_
    have h := hP.mul_mul_conjTranspose_same E
    rwa [hE.eq] at h
  have he : rtr ((1 - E) * Q * (1 - E)) ≤ 0 := rtr_nonpos_of_neg_posSemidef hEneg
  -- rank bounds
  have hEb : rtr E ≤ (b : ℝ) := by
    rw [hEtr]
    exact_mod_cast hb
  have hGr : rtr G ≤ (r : ℝ) := by
    rw [hGtr, posIndex_eq_rank hRpsd]
    have h1 : ((1 - E) * P * (1 - E)).rank ≤ P.rank :=
      le_trans (Matrix.rank_mul_le_left ((1 - E) * P) (1 - E))
        (Matrix.rank_mul_le_right (1 - E) P)
    exact_mod_cast le_trans h1 hr
  -- combine
  have h1 : 0 ≤ c * rtr (E * P * E) := mul_nonneg hc.le ha
  have h2 : 0 ≤ c * (-rtr ((1 - E) * Q * (1 - E))) := mul_nonneg hc.le (by linarith)
  have h3 : 0 ≤ c ^ 2 * ((b : ℝ) - rtr E) := mul_nonneg (by positivity) (by linarith)
  have h4 : 0 ≤ c ^ 2 / 4 * ((r : ℝ) - rtr G) := mul_nonneg (by positivity) (by linarith)
  rw [hAtr] at hbA
  rw [hBtr] at hbB
  nlinarith [hbA, hbB, hge, hPsplit, hQsplit, h1, h2, h3, h4]

end Zeta23Core

