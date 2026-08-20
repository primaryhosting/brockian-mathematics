/-
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
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

namespace Chem

open Finset Matrix

/-- `zeta a = exp (2πi a / 12)`, the `a`-th power of a primitive 12th root of unity. -/

lemma eigenvalue_mem_range {μ : ℂ} {v : Fin 12 → ℂ} (hv : v ≠ 0)
    (h : (SimpleGraph.cycleGraph 12).adjMatrix ℂ *ᵥ v = μ • v) :
    ∃ k : Fin 12, ((2 * Real.cos (2 * Real.pi * k / 12) : ℝ) : ℂ) = μ := by
  by_contra hcon
  push_neg at hcon
  -- the discrete Fourier coefficients of `v`
  set c : Fin 12 → ℂ := fun k => ∑ j : Fin 12, zeta (-((k.val : ℤ) * j.val)) * v j with hc
  have hrec : ∀ j : Fin 12, v (j - 1) + v (j + 1) = μ * v j := by
    intro j
    have := congrFun h j
    rw [adjMatrix_mulVec_cycle] at this
    simpa using this
  have hshift1 : ∀ k : Fin 12,
      ∑ j : Fin 12, zeta (-((k.val : ℤ) * j.val)) * v (j - 1) = zeta (-(k.val : ℤ)) * c k := by
    intro k
    rw [hc, Finset.mul_sum]
    rw [← Fintype.sum_equiv (Equiv.addRight (1 : Fin 12))
      (fun m : Fin 12 => zeta (-((k.val : ℤ) * ((m + 1 : Fin 12).val))) * v m)
      (fun j : Fin 12 => zeta (-((k.val : ℤ) * j.val)) * v (j - 1)) (by intro m; simp)]
    refine Finset.sum_congr rfl ?_
    intro m _
    have hadd : (((m + 1 : Fin 12).val : ℤ)) % 12 = ((m.val : ℤ) + 1) % 12 := by revert m; decide
    have key : zeta (-((k.val : ℤ) * ((m + 1 : Fin 12).val)))
        = zeta (-(k.val : ℤ)) * zeta (-((k.val : ℤ) * m.val)) := by
      rw [← zeta_add]
      refine zeta_periodic ?_
      have := (Int.ModEq.mul_left (k.val : ℤ) hadd).neg
      simpa [Int.ModEq, mul_add] using this
    rw [key]
    ring
  have hshift2 : ∀ k : Fin 12,
      ∑ j : Fin 12, zeta (-((k.val : ℤ) * j.val)) * v (j + 1) = zeta ((k.val : ℤ)) * c k := by
    intro k
    rw [hc, Finset.mul_sum]
    rw [← Fintype.sum_equiv (Equiv.subRight (1 : Fin 12))
      (fun m : Fin 12 => zeta (-((k.val : ℤ) * ((m - 1 : Fin 12).val))) * v m)
      (fun j : Fin 12 => zeta (-((k.val : ℤ) * j.val)) * v (j + 1)) (by intro m; simp)]
    refine Finset.sum_congr rfl ?_
    intro m _
    have hsub : (((m - 1 : Fin 12).val : ℤ)) % 12 = ((m.val : ℤ) - 1) % 12 := by revert m; decide
    have key : zeta (-((k.val : ℤ) * ((m - 1 : Fin 12).val)))
        = zeta ((k.val : ℤ)) * zeta (-((k.val : ℤ) * m.val)) := by
      rw [← zeta_add]
      refine zeta_periodic ?_
      have := (Int.ModEq.mul_left (k.val : ℤ) hsub).neg
      simpa [Int.ModEq, mul_sub] using this
    rw [key]
    ring
  have hcz : ∀ k : Fin 12, c k = 0 := by
    intro k
    have key : μ * c k = (zeta ((k.val : ℤ)) + zeta (-(k.val : ℤ))) * c k := by
      have hexp : μ * c k = ∑ j : Fin 12, zeta (-((k.val : ℤ) * j.val)) * (μ * v j) := by
        rw [hc, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hexp]
      have hsplit : ∀ j : Fin 12, zeta (-((k.val : ℤ) * j.val)) * (μ * v j)
          = zeta (-((k.val : ℤ) * j.val)) * v (j - 1)
            + zeta (-((k.val : ℤ) * j.val)) * v (j + 1) := by
        intro j
        rw [← hrec j]
        ring
      rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib, hshift1, hshift2]
      ring
    have hne : μ - (zeta ((k.val : ℤ)) + zeta (-(k.val : ℤ))) ≠ 0 := by
      intro h0
      refine hcon k ?_
      rw [two_cos_eq k.val]
      linear_combination -h0
    have hzero : (μ - (zeta ((k.val : ℤ)) + zeta (-(k.val : ℤ)))) * c k = 0 := by
      rw [sub_mul, key]; ring
    rcases mul_eq_zero.mp hzero with h0 | h0
    · exact absurd h0 hne
    · exact h0
  -- Fourier inversion forces `v = 0`
  apply hv
  funext j
  have inv : ∑ k : Fin 12, zeta ((k.val : ℤ) * j.val) * c k = 12 * v j := by
    have step : ∀ k : Fin 12, zeta ((k.val : ℤ) * j.val) * c k
        = ∑ j' : Fin 12, zeta ((k.val : ℤ) * ((j.val : ℤ) - j'.val)) * v j' := by
      intro k
      rw [hc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [← mul_assoc, ← zeta_add]
      congr 2
      ring
    rw [Finset.sum_congr rfl (fun k _ => step k), Finset.sum_comm]
    have horth : ∀ j' : Fin 12, ∑ k : Fin 12, zeta ((k.val : ℤ) * ((j.val : ℤ) - j'.val)) * v j'
        = (if ((j.val : ℤ) - j'.val) % 12 = 0 then (12 : ℂ) else 0) * v j' := by
      intro j'
      rw [← Finset.sum_mul, sum_zeta_eq]
    rw [Finset.sum_congr rfl (fun j' _ => horth j')]
    have hif : ∀ j' : Fin 12,
        (if ((j.val : ℤ) - j'.val) % 12 = 0 then (12 : ℂ) else 0) * v j'
          = if j' = j then (12 : ℂ) * v j' else 0 := by
      intro j'
      by_cases hjj : j' = j
      · rw [if_pos ((fin12_sub_emod j j').mpr hjj), if_pos hjj]
      · rw [if_neg (fun hx => hjj ((fin12_sub_emod j j').mp hx)), if_neg hjj, zero_mul]
    rw [Finset.sum_congr rfl (fun j' _ => hif j'), Finset.sum_ite_eq' Finset.univ j
      (fun j' => (12 : ℂ) * v j')]
    simp
  simp only [hcz, mul_zero, Finset.sum_const_zero] at inv
  have h12 : (12 : ℂ) ≠ 0 := by norm_num
  simpa [h12] using (mul_eq_zero.mp inv.symm)

/-- **Hückel theory for a `C₁₂` ring**: the adjacency (Hückel) eigenvalues of the cycle graph
`C₁₂` are exactly the numbers `2 cos (2πk/12)` for `k = 0, …, 11`. -/
