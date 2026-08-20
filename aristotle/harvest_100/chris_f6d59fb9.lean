import Mathlib
/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Chem

open Complex Finset Matrix

/-- A primitive 7-th root of unity. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 7)

lemma zeta_isPrimitiveRoot : IsPrimitiveRoot zeta 7 := by
  have h := Complex.isPrimitiveRoot_exp 7 (by norm_num)
  norm_num at h
  simpa [zeta] using h

lemma zeta_pow_seven : zeta ^ 7 = 1 := zeta_isPrimitiveRoot.pow_eq_one

lemma zeta_pow_mod (n : ℕ) : zeta ^ (n % 7) = zeta ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 7]
  rw [pow_add, pow_mul, zeta_pow_seven, one_pow, one_mul]

/-- The character `j ↦ ζ ^ j` on `Fin 7`. -/
noncomputable def ee (n : Fin 7) : ℂ := zeta ^ n.val

lemma ee_add (a b : Fin 7) : ee (a + b) = ee a * ee b := by
  simp only [ee, Fin.val_add, zeta_pow_mod, pow_add]

lemma ee_zero : ee 0 = 1 := by simp [ee]

lemma ee_ne_zero (a : Fin 7) : ee a ≠ 0 := by
  simp only [ee, zeta]
  exact pow_ne_zero _ (Complex.exp_ne_zero _)

lemma ee_mul (a b : Fin 7) : ee (a * b) = (ee b) ^ (a.val) := by
  simp only [ee, Fin.val_mul, zeta_pow_mod]
  rw [Nat.mul_comm, pow_mul]

lemma ee_ne_one {c : Fin 7} (hc : c ≠ 0) : ee c ≠ 1 :=
  zeta_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (Fin.val_ne_zero_iff.mpr hc) c.isLt

/-- Orthogonality of the characters of `Fin 7`. -/
lemma sum_ee (c : Fin 7) : ∑ k : Fin 7, ee (k * c) = if c = 0 then 7 else 0 := by
  by_cases hc : c = 0
  · subst hc
    simp [ee_zero]
  · simp only [hc, if_false]
    have h1 : ∑ k : Fin 7, ee (k * c) = ∑ m ∈ Finset.range 7, (ee c) ^ m := by
      rw [← Fin.sum_univ_eq_sum_range (fun m => (ee c) ^ m) 7]
      exact Finset.sum_congr rfl fun k _ => ee_mul k c
    have h7 : (ee c) ^ 7 = 1 := by
      simp only [ee]
      rw [← pow_mul, Nat.mul_comm, pow_mul, zeta_pow_seven, one_pow]
    rw [h1, geom_sum_eq (ee_ne_one hc), h7]
    simp

/-- The eigenvalue attached to `k`. -/
noncomputable def lam (k : Fin 7) : ℝ := 2 * Real.cos (2 * Real.pi * k.val / 7)

lemma ee_add_ee_neg (k : Fin 7) : ee k + ee (-k) = (lam k : ℂ) := by
  have hz : ee k = Complex.exp (((2 * Real.pi * k.val / 7 : ℝ) : ℂ) * Complex.I) := by
    simp only [ee, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h : ee k * ee (-k) = 1 := by rw [← ee_add]; simp [ee_zero]
  have hinv : ee (-k) = (ee k)⁻¹ := (DivisionMonoid.inv_eq_of_mul _ _ h).symm
  rw [hinv, hz, ← Complex.exp_neg, lam]
  rw [Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

/-- The adjacency matrix of the cycle graph `C₇` acts on a vector by summing over the two
neighbours of each vertex. -/
lemma adjMatrix_cycleGraph_mulVec (v : Fin 7 → ℂ) (i : Fin 7) :
    ((SimpleGraph.cycleGraph 7).adjMatrix ℂ *ᵥ v) i = v (i - 1) + v (i + 1) := by
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  have hne : ∀ i : Fin 7, i - 1 ≠ i + 1 := by decide
  have hnb : (SimpleGraph.cycleGraph 7).neighborFinset i = {i - 1, i + 1} :=
    SimpleGraph.cycleGraph_neighborFinset (n := 5) (v := i)
  rw [hnb, Finset.sum_pair (hne i)]

/-- The eigenvector attached to `k`. -/
noncomputable def evec (k : Fin 7) : Fin 7 → ℂ := fun j => ee (j * k)

lemma adj_mulVec_evec (k : Fin 7) :
    (SimpleGraph.cycleGraph 7).adjMatrix ℂ *ᵥ (evec k) = (lam k : ℂ) • evec k := by
  funext i
  rw [adjMatrix_cycleGraph_mulVec]
  simp only [evec, Pi.smul_apply, smul_eq_mul]
  rw [← ee_add_ee_neg k]
  have h1 : (i - 1) * k = i * k + (-k) := by decide +revert
  have h2 : (i + 1) * k = i * k + k := by decide +revert
  rw [h1, h2, ee_add, ee_add]
  ring

lemma evec_ne_zero (k : Fin 7) : evec k ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp only [evec, Pi.zero_apply, zero_mul] at h0
  exact ee_ne_zero 0 h0

/-- Fourier inversion on `Fin 7`. -/
lemma fourier_inversion (v : Fin 7 → ℂ) (j : Fin 7) :
    ∑ k : Fin 7, ee (j * k) * (∑ i : Fin 7, ee (-(i * k)) * v i) = 7 * v j := by
  have step : ∀ k : Fin 7, ee (j * k) * (∑ i : Fin 7, ee (-(i * k)) * v i)
      = ∑ i : Fin 7, ee (k * (j - i)) * v i := by
    intro k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : k * (j - i) = j * k + -(i * k) := by decide +revert
    rw [h, ee_add]
    ring
  simp only [step]
  rw [Finset.sum_comm]
  have hrow : ∀ i : Fin 7, ∑ k : Fin 7, ee (k * (j - i)) * v i
      = (if j - i = 0 then (7 : ℂ) else 0) * v i := by
    intro i
    rw [← Finset.sum_mul, sum_ee]
  simp only [hrow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    have h : j - i ≠ 0 := sub_ne_zero_of_ne (Ne.symm hij)
    simp [h]
  · intro h
    exact absurd (Finset.mem_univ j) h

lemma sum_shift_sub (v : Fin 7 → ℂ) (k : Fin 7) :
    ∑ i : Fin 7, ee (-(i * k)) * v (i - 1)
      = ee (-k) * ∑ i : Fin 7, ee (-(i * k)) * v i := by
  rw [← Equiv.sum_comp (Equiv.addRight (1 : Fin 7)) (fun i => ee (-(i * k)) * v (i - 1))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right]
  have h : -((i + 1) * k) = -k + -(i * k) := by decide +revert
  rw [h, ee_add, mul_assoc]

lemma sum_shift_add (v : Fin 7 → ℂ) (k : Fin 7) :
    ∑ i : Fin 7, ee (-(i * k)) * v (i + 1)
      = ee k * ∑ i : Fin 7, ee (-(i * k)) * v i := by
  rw [← Equiv.sum_comp (Equiv.subRight (1 : Fin 7)) (fun i => ee (-(i * k)) * v (i + 1))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Equiv.subRight_apply, sub_add_cancel]
  have h : -((i - 1) * k) = k + -(i * k) := by decide +revert
  rw [h, ee_add, mul_assoc]

/-- **Hückel theory for `C₇`.**  A complex number `μ` is an eigenvalue of the adjacency matrix
of the cycle graph `C₇` if and only if `μ = 2 * cos (2 * π * k / 7)` for some `k ∈ {0, …, 6}`. -/
theorem huckel_C7 (μ : ℂ) :
    (∃ v : Fin 7 → ℂ, v ≠ 0 ∧ (SimpleGraph.cycleGraph 7).adjMatrix ℂ *ᵥ v = μ • v) ↔
      ∃ k : ℕ, k < 7 ∧ μ = ((2 * Real.cos (2 * Real.pi * (k : ℝ) / 7) : ℝ) : ℂ) := by
  constructor
  · rintro ⟨v, hv, hAv⟩
    have hwne : ∃ k : Fin 7, (∑ i : Fin 7, ee (-(i * k)) * v i) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hv
      funext j
      have h := fourier_inversion v j
      simp only [hcon, mul_zero, Finset.sum_const_zero] at h
      exact (mul_eq_zero.mp h.symm).resolve_left (by norm_num)
    obtain ⟨k, hk⟩ := hwne
    have hv1 : ∀ i : Fin 7, v (i - 1) + v (i + 1) = μ * v i := by
      intro i
      have h := congrFun hAv i
      rw [adjMatrix_cycleGraph_mulVec] at h
      simpa using h
    have hmu : μ * (∑ i : Fin 7, ee (-(i * k)) * v i)
        = (lam k : ℂ) * (∑ i : Fin 7, ee (-(i * k)) * v i) := by
      have expand : μ * (∑ i : Fin 7, ee (-(i * k)) * v i)
          = ∑ i : Fin 7, ee (-(i * k)) * (v (i - 1) + v (i + 1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hv1 i]
        ring
      rw [expand]
      simp only [mul_add]
      rw [Finset.sum_add_distrib, sum_shift_sub, sum_shift_add, ← ee_add_ee_neg k]
      ring
    have hμ : μ = (lam k : ℂ) := mul_right_cancel₀ hk hmu
    exact ⟨k.val, k.isLt, by rw [hμ, lam]⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨evec ⟨k, hk⟩, evec_ne_zero _, ?_⟩
    simpa [lam] using adj_mulVec_evec ⟨k, hk⟩

end Chem

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

