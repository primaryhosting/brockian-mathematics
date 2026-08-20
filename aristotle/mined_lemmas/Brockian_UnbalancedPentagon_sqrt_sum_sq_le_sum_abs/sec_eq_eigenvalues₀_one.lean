import Brockian.Fin5
import Brockian.Defs
import Brockian.Rayleigh
import Brockian.Gap
import Brockian.Poincare
import Brockian.LowerBound
import Brockian.LtOne
import Brockian.Perturb
import Brockian.LimitMatrices
import Brockian.FamilyDefs
import Brockian.LimitA
import Brockian.LimitB
import Brockian.GapLimits
import Brockian.Range
import Brockian.Spectrum
import Brockian.OpNorm
import Brockian.MinMax
import Brockian.UnbalancedPentagonLimits

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

import Brockian.LimitA
import Brockian.LimitB
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Operator-norm form of the two matrix limits

The entrywise `ℓ¹` norm `nrm1` dominates the `ℓ²` operator norm of a `5 × 5` real matrix
(`opNorm_le_nrm1`).  Consequently the entrywise convergences `Qa_tendsto_Qmin` and
`Qb_tendsto_Qmax` upgrade to convergence in the operator norm.
-/

namespace Brockian.UnbalancedPentagon

open Matrix Finset Filter Topology
open scoped Matrix.Norms.L2Operator

/-- `√(∑ |wᵢ|²) ≤ ∑ |wᵢ|`. -/

theorem sec_eq_eigenvalues₀_one {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : A.IsHermitian)
    {v : Fin 5 → ℝ} (hv : v ≠ 0) (hvA : A *ᵥ v = hA.eigenvalues₀ 0 • v) :
    sec A v = hA.eigenvalues₀ 1 := by
  obtain ⟨E, horth, heig, hcomp⟩ := exists_eigenbasis A hA
  have hsymm := transpose_eq_of_isHermitian hA
  set lam := hA.eigenvalues₀ with hlam
  have hanti : Antitone lam := hA.eigenvalues₀_antitone
  set d : Fin 5 → ℝ := fun j => E j ⬝ᵥ v with hd
  have hone_le : ∀ j : Fin 5, j ≠ 0 → (1 : Fin 5) ≤ j := by
    intro j hj
    rw [Fin.le_def]
    have : j.val ≠ 0 := fun h => hj (Fin.ext h)
    simp only [Fin.val_one]
    omega
  -- In the case of a simple top eigenvalue, `v` is a multiple of `E 0`.
  have hdzero : lam 1 < lam 0 → ∀ j : Fin 5, j ≠ 0 → d j = 0 := by
    intro hlt j hj
    have h := eigen_coeff_eq_zero hsymm heig hvA j
    have hle : lam j ≤ lam 1 := hanti (hone_le j hj)
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (by intro hz; nlinarith)
    · exact h'
  have hd0 : lam 1 < lam 0 → d 0 ≠ 0 := by
    intro hlt hz
    have hpar := dot_self_eq_sum_coeff_sq hcomp v
    have hzero : ∀ j ∈ Finset.univ, (E j ⬝ᵥ v) ^ 2 = (0:ℝ) := by
      intro j _
      rcases eq_or_ne j 0 with rfl | hj
      · rw [show E 0 ⬝ᵥ v = d 0 from rfl, hz]; ring
      · rw [show E j ⬝ᵥ v = d j from rfl, hdzero hlt j hj]; ring
    rw [Finset.sum_congr rfl hzero] at hpar
    simp only [Finset.sum_const, smul_zero] at hpar
    exact absurd hpar (dot_self_pos hv).ne'
  -- Upper bound.
  have hub : ∀ x : Fin 5 → ℝ, x ⬝ᵥ x = 1 → v ⬝ᵥ x = 0 → x ⬝ᵥ (A *ᵥ x) ≤ lam 1 := by
    intro x hx hxv
    have hexp := rayleigh_eq_sum_eigen heig hcomp x
    have hpar := dot_self_eq_sum_coeff_sq hcomp x
    have hkey : ∀ j : Fin 5, lam j * (E j ⬝ᵥ x) ^ 2 ≤ lam 1 * (E j ⬝ᵥ x) ^ 2 := by
      intro j
      rcases le_or_gt (lam 0) (lam 1) with hcase | hcase
      · have hle : lam j ≤ lam 1 := by
          rcases eq_or_ne j 0 with rfl | hj
          · exact hcase
          · exact hanti (hone_le j hj)
        nlinarith [sq_nonneg (E j ⬝ᵥ x)]
      · rcases eq_or_ne j 0 with rfl | hj
        · have hc0 : E 0 ⬝ᵥ x = 0 := by
            have hsplit : v ⬝ᵥ x = ∑ j, d j * (E j ⬝ᵥ x) := dot_eq_sum_coeff_mul hcomp v x
            rw [hxv] at hsplit
            rw [Finset.sum_eq_single (0 : Fin 5)] at hsplit
            · exact (mul_eq_zero.mp hsplit.symm).resolve_left (hd0 hcase)
            · intro j _ hj
              rw [hdzero hcase j hj]; ring
            · intro hcontra; exact absurd (Finset.mem_univ (0 : Fin 5)) hcontra
          rw [hc0]; ring_nf; rfl
        · have hle : lam j ≤ lam 1 := hanti (hone_le j hj)
          nlinarith [sq_nonneg (E j ⬝ᵥ x)]
    calc x ⬝ᵥ (A *ᵥ x) = ∑ j, lam j * (E j ⬝ᵥ x) ^ 2 := hexp
      _ ≤ ∑ j, lam 1 * (E j ⬝ᵥ x) ^ 2 := Finset.sum_le_sum fun j _ => hkey j
      _ = lam 1 * (x ⬝ᵥ x) := by rw [hpar, Finset.mul_sum]
      _ = lam 1 := by rw [hx, mul_one]
  -- A test vector attaining `lam 1`.
  have hwitness : ∃ w : Fin 5 → ℝ, v ⬝ᵥ w = 0 ∧ 0 < w ⬝ᵥ w ∧
      w ⬝ᵥ (A *ᵥ w) = lam 1 * (w ⬝ᵥ w) := by
    have hcombo : ∀ a b : ℝ, ((a • E 0 + b • E 1) ⬝ᵥ (a • E 0 + b • E 1) = a ^ 2 + b ^ 2) ∧
        (v ⬝ᵥ (a • E 0 + b • E 1) = a * d 0 + b * d 1) ∧
        ((a • E 0 + b • E 1) ⬝ᵥ (A *ᵥ (a • E 0 + b • E 1))
          = lam 0 * a ^ 2 + lam 1 * b ^ 2) := by
      intro a b
      have h01 : E 0 ⬝ᵥ E 1 = 0 := by rw [horth 0 1]; norm_num
      have h10 : E 1 ⬝ᵥ E 0 = 0 := by rw [horth 1 0]; norm_num
      have h00 : E 0 ⬝ᵥ E 0 = 1 := by rw [horth 0 0, if_pos rfl]
      have h11 : E 1 ⬝ᵥ E 1 = 1 := by rw [horth 1 1, if_pos rfl]
      refine ⟨?_, ?_, ?_⟩
      · simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
          smul_eq_mul, h00, h11, h01, h10]
        ring
      · have hv0 : v ⬝ᵥ E 0 = d 0 := by rw [hd]; exact dotProduct_comm _ _
        have hv1 : v ⬝ᵥ E 1 = d 1 := by rw [hd]; exact dotProduct_comm _ _
        simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hv0, hv1]
      · rw [mulVec_add, mulVec_smul, mulVec_smul, heig 0, heig 1]
        simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
          smul_eq_mul, h00, h11, h01, h10]
        ring
    rcases le_or_gt (lam 0) (lam 1) with hcase | hcase
    · -- top eigenvalue is degenerate: pick a vector in `span {E 0, E 1} ∩ v^⊥`
      have heq : lam 0 = lam 1 := le_antisymm hcase (hanti (by norm_num))
      by_cases hboth : d 0 = 0 ∧ d 1 = 0
      · obtain ⟨h0, h1⟩ := hboth
        obtain ⟨hn, ho, hr⟩ := hcombo 1 0
        refine ⟨(1 : ℝ) • E 0 + (0 : ℝ) • E 1, ?_, ?_, ?_⟩
        · rw [ho, h0, h1]; ring
        · rw [hn]; norm_num
        · rw [hr, hn, heq]; ring
      · obtain ⟨hn, ho, hr⟩ := hcombo (d 1) (-(d 0))
        refine ⟨(d 1) • E 0 + (-(d 0)) • E 1, ?_, ?_, ?_⟩
        · rw [ho]; ring
        · rw [hn]
          rcases not_and_or.mp hboth with h | h
          · have := pow_pos (abs_pos.mpr h) 2
            nlinarith [sq_nonneg (d 1), sq_abs (d 0)]
          · have := pow_pos (abs_pos.mpr h) 2
            nlinarith [sq_nonneg (d 0), sq_abs (d 1)]
        · rw [hr, hn, heq]; ring
    · -- simple top eigenvalue: `E 1` works
      refine ⟨E 1, ?_, ?_, ?_⟩
      · rw [dotProduct_comm]
        exact hdzero hcase 1 (by decide)
      · rw [horth 1 1, if_pos rfl]; norm_num
      · rw [heig 1, dotProduct_smul, smul_eq_mul, horth 1 1, if_pos rfl]
  obtain ⟨w, hwv, hwpos, hwR⟩ := hwitness
  have hmem := mem_rayleighSet_of_vec (A := A) hwv hwpos
  rw [hwR, mul_div_assoc, div_self hwpos.ne', mul_one] at hmem
  have hbdd : BddAbove (rayleighSet A v) := by
    refine ⟨lam 1, ?_⟩
    rintro r ⟨x, hx, hp, rfl⟩
    exact hub x hx hp
  refine le_antisymm (csSup_le ⟨_, hmem⟩ ?_) (le_csSup hbdd hmem)
  rintro r ⟨x, hx, hp, rfl⟩
  exact hub x hx hp

/-! ### Specialisation to `Q m` -/

variable {m : Fin 5 → ℝ}

