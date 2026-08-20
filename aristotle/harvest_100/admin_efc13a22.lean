/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Finset

/-- A primitive 11-th root of unity. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 11)

lemma zeta_primitive : IsPrimitiveRoot zeta 11 :=
  Complex.isPrimitiveRoot_exp 11 (by norm_num)

lemma zeta_pow_eleven : zeta ^ (11 : ℕ) = 1 := zeta_primitive.pow_eq_one

/-- The character `x ↦ ζ ^ x` on `ZMod 11`. -/
noncomputable def eps (x : ZMod 11) : ℂ := zeta ^ x.val

/-- The adjacency matrix of the cycle graph `C₁₁`, indexed by `ZMod 11`. -/
def C11 : Matrix (ZMod 11) (ZMod 11) ℂ :=
  fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

lemma eps_zero : eps 0 = 1 := by simp [eps]

lemma zeta_pow_congr {a b : ℕ} (h : a % 11 = b % 11) : zeta ^ a = zeta ^ b := by
  have key : ∀ n : ℕ, zeta ^ n = zeta ^ (n % 11) := by
    intro n
    conv_lhs => rw [← Nat.div_add_mod n 11]
    rw [pow_add, pow_mul, zeta_pow_eleven, one_pow, one_mul]
  rw [key a, key b, h]

lemma eps_add (x y : ZMod 11) : eps (x + y) = eps x * eps y := by
  rw [eps, eps, eps, ← pow_add]
  refine zeta_pow_congr ?_
  rw [ZMod.val_add]
  simp [Nat.mod_mod_of_dvd]

lemma eps_ne_zero (x : ZMod 11) : eps x ≠ 0 := by
  have : zeta ≠ 0 := zeta_primitive.ne_zero (by norm_num)
  exact pow_ne_zero _ this

lemma eps_neg (x : ZMod 11) : eps (-x) = (eps x)⁻¹ := by
  have h : eps (-x) * eps x = 1 := by rw [← eps_add]; simp [eps_zero]
  exact eq_inv_of_mul_eq_one_left h

/-- The value of `eps` in terms of the exponential. -/
lemma eps_eq_exp (x : ZMod 11) :
    eps x = Complex.exp ((2 * Real.pi * (x.val : ℝ) / 11 : ℝ) * Complex.I) := by
  rw [eps, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma eps_add_eps_neg (x : ZMod 11) :
    eps x + eps (-x) = ((2 * Real.cos (2 * Real.pi * (x.val : ℝ) / 11) : ℝ) : ℂ) := by
  have h1 : eps (-x) = Complex.exp (-((2 * Real.pi * (x.val : ℝ) / 11 : ℝ) * Complex.I)) := by
    rw [eps_neg, eps_eq_exp, ← Complex.exp_neg]
  rw [eps_eq_exp x, h1]
  push_cast
  rw [Complex.two_cos, neg_mul]

/-- The action of the adjacency matrix. -/
lemma mulVec_C11 (v : ZMod 11 → ℂ) (i : ZMod 11) :
    C11.mulVec v i = v (i + 1) + v (i - 1) := by
  have hne : (i + 1 : ZMod 11) ≠ i - 1 := by
    intro h
    have : (2 : ZMod 11) = 0 := by linear_combination h
    exact absurd this (by decide)
  have : C11.mulVec v i = ∑ j ∈ ({i + 1, i - 1} : Finset (ZMod 11)), v j := by
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_congr rfl (g := fun j => if j ∈ ({i + 1, i - 1} : Finset (ZMod 11)) then v j else 0)]
    · rw [Finset.sum_ite_mem, Finset.univ_inter]
    · intro j _
      by_cases h : j = i + 1 ∨ j = i - 1 <;> simp [C11, h]
  rw [this, Finset.sum_pair hne]

lemma sum_eps_univ : ∑ k : ZMod 11, eps k = 0 := by
  have h : ∑ k : ZMod 11, eps k = ∑ i ∈ Finset.range 11, zeta ^ i := by
    have h2 : ∑ k : ZMod 11, eps k = ∑ i : Fin 11, zeta ^ (i : ℕ) := rfl
    rw [h2, Fin.sum_univ_eq_sum_range]
  rw [h, zeta_primitive.geom_sum_eq_zero (by norm_num)]

lemma sum_eps_mul (d : ZMod 11) :
    ∑ k : ZMod 11, eps (k * d) = if d = 0 then (11 : ℂ) else 0 := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  by_cases hd : d = 0
  · subst hd
    simp [eps_zero]
  · rw [if_neg hd]
    have h : ∑ k : ZMod 11, eps (k * d) = ∑ k : ZMod 11, eps k :=
      Fintype.sum_equiv (Equiv.mulRight₀ d hd) _ _ (fun _ => rfl)
    rw [h, sum_eps_univ]

/-- The Fourier eigenvectors of the cycle. -/
noncomputable def evec (k : ZMod 11) : ZMod 11 → ℂ := fun j => eps (k * j)

lemma evec_ne_zero (k : ZMod 11) : evec k ≠ 0 := by
  intro h
  have : evec k 0 = 0 := by rw [h]; rfl
  rw [evec, mul_zero, eps_zero] at this
  exact one_ne_zero this

lemma mulVec_evec (k : ZMod 11) :
    C11.mulVec (evec k) = (eps k + eps (-k)) • evec k := by
  funext i
  rw [mulVec_C11]
  have h1 : k * (i + 1) = k * i + k := by ring
  have h2 : k * (i - 1) = k * i + (-k) := by ring
  simp only [evec, Pi.smul_apply, smul_eq_mul, h1, h2, eps_add]
  ring

/-- **Hückel theory for the cycle `C₁₁`.**  The eigenvalues of the adjacency matrix of the
cycle graph on 11 vertices are exactly the numbers `2 cos (2πk/11)`, `k = 0, …, 10`:
each such number is an eigenvalue (with an explicit Fourier eigenvector), and every
eigenvalue is of this form. -/
theorem huckel_C11 :
    (∀ k : Fin 11, ∃ v : ZMod 11 → ℂ, v ≠ 0 ∧
        C11.mulVec v = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 11) : ℝ) : ℂ) • v) ∧
    (∀ (μ : ℂ) (v : ZMod 11 → ℂ), v ≠ 0 → C11.mulVec v = μ • v →
        ∃ k : Fin 11, μ = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 11) : ℝ) : ℂ)) := by
  constructor
  · intro k
    refine ⟨evec (k : ℕ), evec_ne_zero _, ?_⟩
    rw [mulVec_evec, eps_add_eps_neg]
    congr 3
    rw [ZMod.val_natCast_of_lt k.isLt]
  · intro μ v hv hvμ
    set w : ZMod 11 → ℂ := fun k => ∑ j : ZMod 11, v j * eps (-(k * j)) with hw
    -- Fourier coefficients satisfy the eigenvalue relation
    have key : ∀ k : ZMod 11, μ * w k = (eps k + eps (-k)) * w k := by
      intro k
      have hstep : μ * w k = ∑ j : ZMod 11, (v (j + 1) + v (j - 1)) * eps (-(k * j)) := by
        rw [hw, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have : μ * v j = v (j + 1) + v (j - 1) := by
          have := congrFun hvμ j
          rw [mulVec_C11] at this
          simpa [Pi.smul_apply, smul_eq_mul] using this.symm
        rw [← mul_assoc, this]
      have hS1 : ∑ j : ZMod 11, v (j + 1) * eps (-(k * j)) = eps k * w k := by
        have e1 : ∑ j : ZMod 11, v (j + 1) * eps (-(k * j))
            = ∑ m : ZMod 11, v m * eps (-(k * (m - 1))) := by
          refine Fintype.sum_equiv (Equiv.addRight (1 : ZMod 11)) _ _ (fun j => ?_)
          simp
        rw [e1, hw, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        have : -(k * (m - 1)) = -(k * m) + k := by ring
        rw [this, eps_add]
        ring
      have hS2 : ∑ j : ZMod 11, v (j - 1) * eps (-(k * j)) = eps (-k) * w k := by
        have e1 : ∑ j : ZMod 11, v (j - 1) * eps (-(k * j))
            = ∑ m : ZMod 11, v m * eps (-(k * (m + 1))) := by
          refine Fintype.sum_equiv (Equiv.subRight (1 : ZMod 11)) _ _ (fun j => ?_)
          simp
        rw [e1, hw, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        have : -(k * (m + 1)) = -(k * m) + (-k) := by ring
        rw [this, eps_add]
        ring
      rw [hstep]
      simp only [add_mul]
      rw [Finset.sum_add_distrib, hS1, hS2]
    -- some Fourier coefficient is nonzero
    have hex : ∃ k : ZMod 11, w k ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hv
      funext j
      have hinv : (11 : ℂ) * v j = ∑ k : ZMod 11, w k * eps (k * j) := by
        have step1 : ∑ k : ZMod 11, w k * eps (k * j)
            = ∑ m : ZMod 11, v m * ∑ k : ZMod 11, eps (k * (j - m)) := by
          rw [hw]
          simp only [Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          have : k * (j - m) = -(k * m) + k * j := by ring
          rw [this, eps_add]
          ring
        rw [step1]
        have step2 : ∀ m : ZMod 11, v m * ∑ k : ZMod 11, eps (k * (j - m))
            = if m = j then (11 : ℂ) * v j else 0 := by
          intro m
          rw [sum_eps_mul]
          by_cases hm : m = j
          · subst hm; simp [mul_comm]
          · have : j - m ≠ 0 := sub_ne_zero_of_ne (Ne.symm hm)
            simp [this, hm]
        rw [Finset.sum_congr rfl (fun m _ => step2 m), Finset.sum_ite_eq' Finset.univ j]
        simp
      simp only [hcon, zero_mul, Finset.sum_const_zero] at hinv
      have h11 : (11 : ℂ) ≠ 0 := by norm_num
      simp only [Pi.zero_apply]
      exact (mul_eq_zero.1 hinv).resolve_left h11
    obtain ⟨k, hk⟩ := hex
    refine ⟨⟨k.val, ZMod.val_lt k⟩, ?_⟩
    have hμ : μ = eps k + eps (-k) := by
      have h3 : (μ - (eps k + eps (-k))) * w k = 0 := by linear_combination key k
      exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hk)
    rw [hμ, eps_add_eps_neg]

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

