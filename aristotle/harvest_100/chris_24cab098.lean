/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Finset Complex

noncomputable section

/-- A primitive 11-th root of unity. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 11)

/-- The standard additive character of `ZMod 11` with values in `ℂ`. -/
noncomputable def chi (x : ZMod 11) : ℂ := zeta ^ x.val

/-- The adjacency matrix of the cycle graph `C₁₁`, as a circulant matrix indexed by
`ZMod 11`: vertices `i` and `j` are adjacent iff `i - j = ±1`. -/
noncomputable def C11 : Matrix (ZMod 11) (ZMod 11) ℂ :=
  Matrix.circulant (fun d => if d = 1 ∨ d = -1 then 1 else 0)

lemma zeta_pow_eleven : zeta ^ 11 = 1 := by
  have := Complex.isPrimitiveRoot_exp 11 (by norm_num)
  simpa [zeta] using this.pow_eq_one

lemma zeta_pow_mod (n : ℕ) : zeta ^ (n % 11) = zeta ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 11]
  rw [pow_add, pow_mul, zeta_pow_eleven, one_pow, one_mul]

lemma chi_zero : chi 0 = 1 := by simp [chi]

lemma chi_add (x y : ZMod 11) : chi (x + y) = chi x * chi y := by
  simp only [chi, ZMod.val_add, zeta_pow_mod, pow_add]

lemma chi_ne_zero (x : ZMod 11) : chi x ≠ 0 := by
  refine pow_ne_zero _ ?_
  simp [zeta, Complex.exp_ne_zero]

lemma chi_neg (x : ZMod 11) : chi (-x) = (chi x)⁻¹ := by
  have h : chi (-x) * chi x = 1 := by rw [← chi_add]; simp [chi_zero]
  exact eq_inv_of_mul_eq_one_left h

lemma sum_chi : ∑ x : ZMod 11, chi x = 0 := by
  have h : ∑ x : ZMod 11, chi x = ∑ i ∈ Finset.range 11, zeta ^ i := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_nbij' (fun x => (⟨x.val, x.val_lt⟩ : Fin 11)) (fun i => (i.val : ZMod 11))
      (by intros; simp) (by intros; simp)
      (by intro a _; simp)
      (by intro a _; ext; simp [ZMod.val_natCast_of_lt a.isLt])
      (by intro a _; simp [chi])
  rw [h]
  have hprim := Complex.isPrimitiveRoot_exp 11 (by norm_num)
  have : zeta ≠ 1 := by
    intro hz
    have := hprim.ne_one (by norm_num)
    exact this (by simpa [zeta] using hz)
  have hgeom : (zeta - 1) * ∑ i ∈ Finset.range 11, zeta ^ i = zeta ^ 11 - 1 :=
    (geom_sum_mul zeta 11) ▸ (mul_comm _ _)
  rw [zeta_pow_eleven, sub_self] at hgeom
  rcases mul_eq_zero.1 hgeom with h1 | h2
  · exact absurd (sub_eq_zero.1 h1) this
  · exact h2

lemma sum_chi_mul (d : ZMod 11) (hd : d ≠ 0) : ∑ k : ZMod 11, chi (k * d) = 0 := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have := Equiv.sum_comp (Equiv.mulRight₀ d hd) chi
  simpa [Equiv.mulRight₀] using this.trans sum_chi

lemma sum_chi_mul_ite (d : ZMod 11) :
    ∑ k : ZMod 11, chi (k * d) = if d = 0 then 11 else 0 := by
  by_cases h : d = 0
  · subst h; simp [chi_zero]
  · simp [h, sum_chi_mul d h]

lemma C11_mulVec (v : ZMod 11 → ℂ) (i : ZMod 11) :
    (C11.mulVec v) i = v (i - 1) + v (i + 1) := by
  have hne : (i - 1 : ZMod 11) ≠ i + 1 := by
    intro h
    have : (2 : ZMod 11) = 0 := by linear_combination -h
    revert this
    decide
  have hstep : ∀ j : ZMod 11,
      (if i - j = 1 ∨ i - j = -1 then (1 : ℂ) else 0) * v j
        = if j ∈ ({i - 1, i + 1} : Finset (ZMod 11)) then v j else 0 := by
    intro j
    by_cases h1 : i - j = 1
    · have : j = i - 1 := by linear_combination -h1
      simp [this]
    · by_cases h2 : i - j = -1
      · have : j = i + 1 := by linear_combination -h2
        simp [this, hne.symm]
      · have hj1 : j ≠ i - 1 := by
          intro h; exact h1 (by rw [h]; ring)
        have hj2 : j ≠ i + 1 := by
          intro h; exact h2 (by rw [h]; ring)
        simp [h1, h2, hj1, hj2]
  simp only [Matrix.mulVec, dotProduct, C11, Matrix.circulant_apply]
  rw [Finset.sum_congr rfl (fun j _ => hstep j), Finset.sum_ite_mem,
    Finset.univ_inter, Finset.sum_pair hne]

/-- The eigenvalue attached to the character index `k`. -/
lemma chi_add_chi_neg (k : Fin 11) :
    chi ((k : ℕ) : ZMod 11) + chi (-((k : ℕ) : ZMod 11))
      = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 11) : ℝ) : ℂ) := by
  set θ : ℝ := 2 * Real.pi * (k : ℕ) / 11 with hθ
  have hval : (((k : ℕ) : ZMod 11)).val = (k : ℕ) := ZMod.val_natCast_of_lt k.isLt
  have hchi : chi ((k : ℕ) : ZMod 11) = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [chi, hval, zeta, ← Complex.exp_nat_mul]
    congr 1
    rw [hθ]
    push_cast
    ring
  rw [chi_neg, hchi, ← Complex.exp_neg]
  have : ((2 * Real.cos θ : ℝ) : ℂ) = 2 * Complex.cos (θ : ℂ) := by
    push_cast [Complex.ofReal_cos]
    ring
  rw [this, Complex.two_cos]
  ring_nf

/-- **Hückel theory for the cycle `C₁₁`.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₁` if and only if `μ = 2 cos (2πk/11)` for some
`k = 0, 1, …, 10`. -/
theorem huckel_C11 (μ : ℂ) :
    (∃ v : ZMod 11 → ℂ, v ≠ 0 ∧ C11.mulVec v = μ • v) ↔
      ∃ k : Fin 11, μ = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 11) : ℝ) : ℂ) := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    -- Fourier coefficients of `v`
    set c : ZMod 11 → ℂ := fun k => ∑ j : ZMod 11, v j * chi (-(k * j)) with hc
    -- Fourier inversion
    have hinv : ∀ j : ZMod 11, ∑ k : ZMod 11, c k * chi (k * j) = 11 * v j := by
      intro j
      have : ∀ k : ZMod 11, c k * chi (k * j)
          = ∑ m : ZMod 11, v m * chi (k * (j - m)) := by
        intro k
        rw [hc]
        simp only [Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [mul_assoc, ← chi_add]
        ring_nf
      rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_comm]
      have : ∀ m : ZMod 11, ∑ k : ZMod 11, v m * chi (k * (j - m))
          = v m * (if j - m = 0 then (11 : ℂ) else 0) := by
        intro m
        rw [← Finset.mul_sum, sum_chi_mul_ite]
      rw [Finset.sum_congr rfl fun m _ => this m]
      simp only [sub_eq_zero, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      ring
    -- some Fourier coefficient is nonzero
    have hex : ∃ k : ZMod 11, c k ≠ 0 := by
      by_contra h
      push_neg at h
      apply hv0
      funext j
      have := hinv j
      simp [h] at this
      simp [this.symm]
    obtain ⟨k, hk⟩ := hex
    -- the eigenvalue equation transported to Fourier coefficients
    have hrel : ∀ i : ZMod 11, v (i - 1) + v (i + 1) = μ * v i := by
      intro i
      have := congrFun hv i
      rw [C11_mulVec] at this
      simpa [Pi.smul_apply, smul_eq_mul] using this
    have key : μ * c k = (chi (-k) + chi k) * c k := by
      have h1 : ∑ j : ZMod 11, v (j - 1) * chi (-(k * j)) = chi (-k) * c k := by
        have := Equiv.sum_comp (Equiv.addRight (1 : ZMod 11))
          (fun j : ZMod 11 => v (j - 1) * chi (-(k * j)))
        rw [← this]
        rw [hc, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [Equiv.coe_addRight, add_sub_cancel_right]
        rw [show -(k * (m + 1)) = -k + -(k * m) by ring, chi_add]
        ring
      have h2 : ∑ j : ZMod 11, v (j + 1) * chi (-(k * j)) = chi k * c k := by
        have := Equiv.sum_comp (Equiv.addRight (-1 : ZMod 11))
          (fun j : ZMod 11 => v (j + 1) * chi (-(k * j)))
        rw [← this]
        rw [hc, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [Equiv.coe_addRight]
        rw [show m + -1 + 1 = m by ring, show -(k * (m + -1)) = k + -(k * m) by ring, chi_add]
        ring
      have h3 : ∑ j : ZMod 11, (v (j - 1) + v (j + 1)) * chi (-(k * j))
          = μ * c k := by
        rw [hc, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hrel j]
        ring
      rw [← h3]
      simp only [add_mul, Finset.sum_add_distrib, h1, h2]
    have hμ : μ = chi (-k) + chi k := mul_right_cancel₀ hk key
    refine ⟨⟨k.val, k.val_lt⟩, ?_⟩
    have hkk : ((k.val : ℕ) : ZMod 11) = k := by
      simp [ZMod.natCast_val, ZMod.cast_id]
    rw [hμ]
    have := chi_add_chi_neg ⟨k.val, k.val_lt⟩
    rw [hkk] at this
    rw [add_comm]
    exact this
  · rintro ⟨k, rfl⟩
    refine ⟨fun j => chi (((k : ℕ) : ZMod 11) * j), ?_, ?_⟩
    · intro h
      have := congrFun h 0
      simp [chi_zero] at this
    · funext i
      rw [C11_mulVec]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← chi_add_chi_neg k]
      set κ : ZMod 11 := ((k : ℕ) : ZMod 11)
      rw [show κ * (i - 1) = -κ + κ * i by ring, show κ * (i + 1) = κ + κ * i by ring,
        chi_add, chi_add]
      ring

end

end Chem

#print axioms Chem.huckel_C11

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

