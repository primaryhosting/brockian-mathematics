/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open scoped Real
open Finset

instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- A primitive 17-th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 17)

lemma om_prim : IsPrimitiveRoot om 17 := Complex.isPrimitiveRoot_exp 17 (by norm_num)

lemma om_pow_17 : om ^ (17 : ℕ) = 1 := om_prim.pow_eq_one

lemma om_pow_congr {m n : ℕ} (h : m % 17 = n % 17) : om ^ m = om ^ n := by
  conv_lhs => rw [← Nat.div_add_mod m 17]
  conv_rhs => rw [← Nat.div_add_mod n 17]
  rw [pow_add, pow_add, pow_mul, pow_mul, om_pow_17, one_pow, one_pow, h]

/-- The additive character `k ↦ ω^k` on `ZMod 17`. -/
noncomputable def ee (m : ZMod 17) : ℂ := om ^ m.val

lemma ee_zero : ee 0 = 1 := by simp [ee]

lemma ee_add (a b : ZMod 17) : ee (a + b) = ee a * ee b := by
  rw [ee, ee, ee, ← pow_add]
  exact om_pow_congr (by rw [ZMod.val_add]; simp)

lemma ee_ne_zero (a : ZMod 17) : ee a ≠ 0 := by
  simp [ee, om, Complex.exp_ne_zero]

lemma ee_neg (a : ZMod 17) : ee (-a) = (ee a)⁻¹ := by
  have h : ee (-a) * ee a = 1 := by rw [← ee_add]; simp [ee_zero]
  exact eq_inv_of_mul_eq_one_left h

lemma ee_natCast (k : ℕ) : ee (k : ZMod 17) = om ^ k := by
  rw [ee]
  exact om_pow_congr (by simp [ZMod.val_natCast])

/-- Orthogonality of the characters. -/
lemma ee_sum (d : ZMod 17) : ∑ k : ZMod 17, ee (k * d) = if d = 0 then 17 else 0 := by
  by_cases hd : d = 0
  · subst hd
    simp [ee_zero]
  · rw [if_neg hd]
    have hbij : ∑ k : ZMod 17, ee (k * d) = ∑ k : ZMod 17, ee k :=
      Equiv.sum_comp (Equiv.mulRight₀ d hd) ee
    rw [hbij]
    have h2 : ∑ k : ZMod 17, ee k = ∑ j ∈ Finset.range 17, om ^ j := by
      rw [Finset.sum_nbij' (i := fun (k : ZMod 17) => k.val) (j := fun (j : ℕ) => (j : ZMod 17))]
      · intro a _; simp [ZMod.val_lt]
      · intro a _; simp
      · intro a _; simp
      · intro a ha; simp only [Finset.mem_range] at ha
        simp [ZMod.val_natCast, Nat.mod_eq_of_lt ha]
      · intro a _; rfl
    rw [h2]
    exact om_prim.geom_sum_eq_zero (by norm_num)

/-- The adjacency matrix of the cycle graph `C₁₇`, with vertices indexed by `ZMod 17`. -/
def adjC17 : Matrix (ZMod 17) (ZMod 17) ℂ :=
  Matrix.of fun i j => if i - j = 1 ∨ j - i = 1 then 1 else 0

lemma adjC17_apply (i j : ZMod 17) :
    adjC17 i j = if j = i - 1 ∨ j = i + 1 then 1 else 0 := by
  have hiff : (i - j = 1 ∨ j - i = 1) ↔ (j = i - 1 ∨ j = i + 1) := by
    constructor
    · rintro (h | h)
      · exact Or.inl (by linear_combination -h)
      · exact Or.inr (by linear_combination h)
    · rintro (h | h)
      · exact Or.inl (by linear_combination -h)
      · exact Or.inr (by linear_combination h)
  simp only [adjC17, Matrix.of_apply, hiff]

lemma adj_mulVec (f : ZMod 17 → ℂ) (i : ZMod 17) :
    adjC17.mulVec f i = f (i - 1) + f (i + 1) := by
  have hne : (i - 1 : ZMod 17) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 17) = 0 := by linear_combination -h
    revert h2; decide
  have key : ∀ j : ZMod 17, adjC17 i j * f j
      = (if j = i - 1 then f j else 0) + (if j = i + 1 then f j else 0) := by
    intro j
    rw [adjC17_apply]
    by_cases hA : j = i - 1
    · have hB : j ≠ i + 1 := by rw [hA]; exact hne
      simp [hA, hne]
    · by_cases hB : j = i + 1
      · simp [hB, Ne.symm hne]
      · simp [hA, hB]
  simp only [Matrix.mulVec, dotProduct, key]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (i - 1) f,
    Finset.sum_ite_eq' Finset.univ (i + 1) f]
  simp

lemma eigenvalue_eq (k : ℕ) :
    ee (k : ZMod 17) + ee (-(k : ZMod 17))
      = ((2 * Real.cos (2 * Real.pi * k / 17) : ℝ) : ℂ) := by
  have hom : om ^ k = Complex.exp ((2 * Real.pi * k / 17 : ℝ) * Complex.I) := by
    rw [om, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h1 : ee ((k : ℕ) : ZMod 17) = Complex.exp ((2 * Real.pi * k / 17 : ℝ) * Complex.I) := by
    rw [ee_natCast, hom]
  have h2 : ee (-((k : ℕ) : ZMod 17))
      = Complex.exp (-((2 * Real.pi * k / 17 : ℝ) * Complex.I)) := by
    rw [ee_neg, h1, ← Complex.exp_neg]
  rw [h1, h2, Complex.ofReal_mul, Complex.ofReal_cos, Complex.ofReal_ofNat, Complex.two_cos]
  ring_nf

/-- **Hückel theory for the cycle `C₁₇`**: a complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph on 17 vertices if and only if it is of the form
`2 cos (2πk/17)` for some `k ∈ {0, …, 16}`. -/
theorem huckel_C17 (mu : ℂ) :
    (∃ v : ZMod 17 → ℂ, v ≠ 0 ∧ adjC17.mulVec v = mu • v)
      ↔ ∃ k : ℕ, k < 17 ∧ mu = ((2 * Real.cos (2 * Real.pi * k / 17) : ℝ) : ℂ) := by
  constructor
  · rintro ⟨u, hu0, hu⟩
    -- Fourier coefficients of the eigenvector
    set c : ZMod 17 → ℂ := fun k => ∑ i : ZMod 17, u i * ee (-(k * i)) with hc
    have hEig : ∀ k : ZMod 17, mu * c k = (ee k + ee (-k)) * c k := by
      intro k
      have hstep : ∀ i : ZMod 17, mu * u i = u (i - 1) + u (i + 1) := by
        intro i
        have hi := congrFun hu i
        simp only [Pi.smul_apply, smul_eq_mul] at hi
        rw [← hi, adj_mulVec]
      have h1 : mu * c k = ∑ i : ZMod 17, (u (i - 1) + u (i + 1)) * ee (-(k * i)) := by
        rw [hc, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← mul_assoc, hstep i]
      have h2 : ∑ i : ZMod 17, u (i - 1) * ee (-(k * i)) = ee (-k) * c k := by
        rw [← Equiv.sum_comp (Equiv.addRight (1 : ZMod 17))
          (fun i => u (i - 1) * ee (-(k * i)))]
        rw [hc, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Equiv.coe_addRight, add_sub_cancel_right]
        have hkk : -(k * (i + 1)) = -k + -(k * i) := by ring
        rw [hkk, ee_add]
        ring
      have h3 : ∑ i : ZMod 17, u (i + 1) * ee (-(k * i)) = ee k * c k := by
        rw [← Equiv.sum_comp (Equiv.addRight (-1 : ZMod 17))
          (fun i => u (i + 1) * ee (-(k * i)))]
        rw [hc, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Equiv.coe_addRight, neg_add_cancel_right]
        have hkk : -(k * (i + -1)) = k + -(k * i) := by ring
        rw [hkk, ee_add]
        ring
      rw [h1]
      simp only [add_mul]
      rw [Finset.sum_add_distrib, h2, h3]
      ring
    have hex : ∃ k : ZMod 17, c k ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply hu0
      funext i
      show u i = 0
      have hsum : ∑ k : ZMod 17, c k * ee (k * i) = 17 * u i := by
        have hswap : ∑ k : ZMod 17, c k * ee (k * i)
            = ∑ j : ZMod 17, u j * ∑ k : ZMod 17, ee (k * (i - j)) := by
          rw [hc]
          simp only [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
          have hkk : k * (i - j) = -(k * j) + k * i := by ring
          rw [hkk, ee_add]
          ring
        rw [hswap]
        have h4 : ∀ j : ZMod 17, u j * ∑ k : ZMod 17, ee (k * (i - j))
            = if j = i then 17 * u i else 0 := by
          intro j
          rw [ee_sum]
          by_cases hj : j = i
          · subst hj; simp [mul_comm]
          · have hij : i - j ≠ 0 := sub_ne_zero_of_ne (Ne.symm hj)
            simp [hij, hj]
        rw [Finset.sum_congr rfl fun j _ => h4 j, Finset.sum_ite_eq' Finset.univ i]
        simp
      have hzero : ∑ k : ZMod 17, c k * ee (k * i) = 0 :=
        Finset.sum_eq_zero fun k _ => by rw [hall k, zero_mul]
      rw [hzero] at hsum
      rcases mul_eq_zero.mp hsum.symm with h | h
      · norm_num at h
      · exact h
    obtain ⟨k, hk⟩ := hex
    refine ⟨k.val, ZMod.val_lt k, ?_⟩
    have hmu : mu = ee k + ee (-k) := mul_right_cancel₀ hk (hEig k)
    rw [hmu, ← eigenvalue_eq k.val]
    simp [ZMod.natCast_val, ZMod.cast_id]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨fun i => ee ((k : ZMod 17) * i), ?_, ?_⟩
    · intro h
      have h0 := congrFun h 0
      simp only [mul_zero, ee_zero, Pi.zero_apply] at h0
      exact one_ne_zero h0
    · funext i
      rw [adj_mulVec]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← eigenvalue_eq k]
      have e1 : (k : ZMod 17) * (i - 1) = -(k : ZMod 17) + (k : ZMod 17) * i := by ring
      have e2 : (k : ZMod 17) * (i + 1) = (k : ZMod 17) + (k : ZMod 17) * i := by ring
      rw [e1, e2, ee_add, ee_add]
      ring

/-- Spectrum form of the same result: the spectrum of the linear map given by the adjacency
matrix of `C₁₇` is exactly `{2 cos (2πk/17) : k = 0, …, 16}`. -/
theorem huckel_C17_spectrum :
    spectrum ℂ (Matrix.toLin' adjC17)
      = {mu : ℂ | ∃ k : ℕ, k < 17 ∧ mu = ((2 * Real.cos (2 * Real.pi * k / 17) : ℝ) : ℂ)} := by
  ext mu
  rw [Set.mem_setOf_eq, ← Module.End.hasEigenvalue_iff_mem_spectrum, ← huckel_C17 mu]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    refine ⟨v, hv.2, ?_⟩
    simpa [Matrix.toLin'_apply] using Module.End.mem_eigenspace_iff.mp hv.1
  · rintro ⟨v, hv0, hv⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr ?_, hv0⟩
    simpa [Matrix.toLin'_apply] using hv

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

