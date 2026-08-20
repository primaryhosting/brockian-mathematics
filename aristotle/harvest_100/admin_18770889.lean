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
noncomputable def zeta (a : ℤ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / 12)

lemma zeta_ne_zero (a : ℤ) : zeta a ≠ 0 := Complex.exp_ne_zero _

lemma zeta_add (a b : ℤ) : zeta (a + b) = zeta a * zeta b := by
  simp only [zeta, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma zeta_zero : zeta 0 = 1 := by simp [zeta]

lemma zeta_eq_zpow (a : ℤ) : zeta a = zeta 1 ^ a := by
  have h : (2 * Real.pi * Complex.I * (a : ℂ) / 12)
      = (a : ℂ) * (2 * Real.pi * Complex.I * ((1 : ℤ) : ℂ) / 12) := by
    push_cast; ring
  rw [zeta, h, Complex.exp_int_mul]
  rfl

lemma zeta_twelve : zeta 12 = 1 := by
  have h : (2 * Real.pi * Complex.I * ((12 : ℤ) : ℂ) / 12) = 2 * Real.pi * Complex.I := by
    push_cast; ring
  rw [zeta, h, Complex.exp_two_pi_mul_I]

lemma zeta_one_pow_twelve : zeta 1 ^ (12 : ℤ) = 1 := by
  rw [← zeta_eq_zpow]; exact zeta_twelve

lemma zeta_periodic {a b : ℤ} (h : a % 12 = b % 12) : zeta a = zeta b := by
  obtain ⟨n, rfl⟩ : ∃ n, a = b + 12 * n := ⟨(a - b) / 12, by omega⟩
  rw [zeta_add, zeta_eq_zpow (12 * n), _root_.zpow_mul, zeta_one_pow_twelve, _root_.one_zpow, mul_one]

lemma zeta_eq_one_iff {d : ℤ} : zeta d = 1 ↔ d % 12 = 0 := by
  rw [zeta, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    have hd : d = 12 * n := by
      field_simp at hn
      exact_mod_cast hn
    omega
  · intro hd
    refine ⟨d / 12, ?_⟩
    have hdd : d = 12 * (d / 12) := by omega
    have hc : ((d : ℂ)) = 12 * ((d / 12 : ℤ) : ℂ) := by
      exact_mod_cast congrArg (fun x : ℤ => (x : ℂ)) hdd
    rw [hc]
    ring

/-- `2 cos (2πm/12)` written in terms of roots of unity. -/
lemma two_cos_eq (m : ℕ) :
    ((2 * Real.cos (2 * Real.pi * m / 12) : ℝ) : ℂ) = zeta (m : ℤ) + zeta (-(m : ℤ)) := by
  have h : ((2 * Real.cos (2 * Real.pi * m / 12) : ℝ) : ℂ)
      = 2 * Complex.cos ((2 * Real.pi * m / 12 : ℝ) : ℂ) := by
    push_cast [Complex.ofReal_cos]
    ring
  rw [h, Complex.two_cos, zeta, zeta]
  congr 1 <;> · congr 1; push_cast; ring

/-- Multiplying by the adjacency matrix of `C₁₂` adds the two cyclic neighbours. -/
lemma adjMatrix_mulVec_cycle (v : Fin 12 → ℂ) (i : Fin 12) :
    ((SimpleGraph.cycleGraph 12).adjMatrix ℂ *ᵥ v) i = v (i - 1) + v (i + 1) := by
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  have hnb : (SimpleGraph.cycleGraph 12).neighborFinset i = {i - 1, i + 1} := by
    exact SimpleGraph.cycleGraph_neighborFinset (n := 10)
  rw [hnb, Finset.sum_pair (by revert i; decide)]

/-- The discrete Fourier orthogonality relation. -/
lemma sum_zeta_eq (d : ℤ) :
    ∑ k : Fin 12, zeta ((k.val : ℤ) * d) = if d % 12 = 0 then 12 else 0 := by
  have hq : ∀ k : Fin 12, zeta ((k.val : ℤ) * d) = zeta d ^ k.val := by
    intro k
    rw [zeta_eq_zpow ((k.val : ℤ) * d), zeta_eq_zpow d, ← zpow_natCast (zeta 1 ^ d) k.val,
      ← _root_.zpow_mul]
    congr 1
    ring
  simp only [hq]
  rw [Fin.sum_univ_eq_sum_range (fun k => zeta d ^ k) 12]
  by_cases h : d % 12 = 0
  · rw [if_pos h, zeta_eq_one_iff.mpr h]
    simp
  · rw [if_neg h]
    have h1 : zeta d ≠ 1 := fun hc => h (zeta_eq_one_iff.mp hc)
    rw [geom_sum_eq h1]
    have h12 : zeta d ^ (12 : ℕ) = 1 := by
      rw [zeta_eq_zpow d, ← zpow_natCast (zeta 1 ^ d) 12, ← _root_.zpow_mul,
        show (d * ((12 : ℕ) : ℤ)) = 12 * d by push_cast; ring, _root_.zpow_mul,
        zeta_one_pow_twelve, _root_.one_zpow]
    rw [h12]
    simp

lemma fin12_sub_emod (j j' : Fin 12) : (((j.val : ℤ) - j'.val) % 12 = 0) ↔ j' = j := by
  revert j j'
  decide

/-- The Fourier vector for index `k` is an eigenvector with eigenvalue `2 cos (2πk/12)`. -/
lemma mulVec_fourier (k : Fin 12) :
    (SimpleGraph.cycleGraph 12).adjMatrix ℂ *ᵥ (fun j : Fin 12 => zeta ((k.val : ℤ) * j.val))
      = ((2 * Real.cos (2 * Real.pi * k / 12) : ℝ) : ℂ) •
          (fun j : Fin 12 => zeta ((k.val : ℤ) * j.val)) := by
  funext i
  rw [adjMatrix_mulVec_cycle]
  have hsub : ∀ i : Fin 12, (((i - 1 : Fin 12).val : ℤ)) % 12 = ((i.val : ℤ) - 1) % 12 := by
    decide
  have hadd : ∀ i : Fin 12, (((i + 1 : Fin 12).val : ℤ)) % 12 = ((i.val : ℤ) + 1) % 12 := by
    decide
  have e1 : zeta ((k.val : ℤ) * ((i - 1 : Fin 12).val))
      = zeta ((k.val : ℤ) * i.val) * zeta (-(k.val : ℤ)) := by
    rw [← zeta_add]
    refine zeta_periodic ?_
    have := (Int.ModEq.mul_left (k.val : ℤ) (hsub i))
    simpa [Int.ModEq, mul_sub] using this
  have e2 : zeta ((k.val : ℤ) * ((i + 1 : Fin 12).val))
      = zeta ((k.val : ℤ) * i.val) * zeta ((k.val : ℤ)) := by
    rw [← zeta_add]
    refine zeta_periodic ?_
    have := (Int.ModEq.mul_left (k.val : ℤ) (hadd i))
    simpa [Int.ModEq, mul_add] using this
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [e1, e2, two_cos_eq k.val]
  ring

/-- Every eigenvalue of the adjacency matrix of `C₁₂` is one of the `2 cos (2πk/12)`. -/
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
theorem huckel_C12 :
    {μ : ℂ | ∃ v : Fin 12 → ℂ, v ≠ 0 ∧
        (SimpleGraph.cycleGraph 12).adjMatrix ℂ *ᵥ v = μ • v}
      = Set.range (fun k : Fin 12 => ((2 * Real.cos (2 * Real.pi * k / 12) : ℝ) : ℂ)) := by
  ext μ
  constructor
  · rintro ⟨v, hv, h⟩
    exact eigenvalue_mem_range hv h
  · rintro ⟨k, rfl⟩
    refine ⟨fun j : Fin 12 => zeta ((k.val : ℤ) * j.val), ?_, mulVec_fourier k⟩
    intro hzero
    have := congrFun hzero 0
    simp [zeta_zero] at this

end Chem

