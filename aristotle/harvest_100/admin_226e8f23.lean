/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hückel theory for the C₁₄ ring

The adjacency eigenvalues of the cycle graph `C₁₄` are exactly the numbers
`2 * cos (2πk/14)` for `k = 0, …, 13`.
-/

namespace Chem

open Finset Complex

/-- A primitive 14-th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 14)

lemma om_isPrimitiveRoot : IsPrimitiveRoot om 14 := by
  have h := Complex.isPrimitiveRoot_exp 14 (by norm_num)
  simpa [om] using h

lemma om_pow_14 : om ^ 14 = 1 := om_isPrimitiveRoot.pow_eq_one

lemma om_pow_mod (a : ℕ) : om ^ (a % 14) = om ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a 14]
  rw [pow_add, pow_mul, om_pow_14, one_pow, one_mul]

/-- The additive character `x ↦ ω ^ x` of `Fin 14`, where `ω = exp (2πi/14)`. -/
noncomputable def ch (x : Fin 14) : ℂ := om ^ x.val

lemma ch_add (x y : Fin 14) : ch (x + y) = ch x * ch y := by
  simp only [ch, Fin.val_add, om_pow_mod, pow_add]

lemma ch_zero : ch 0 = 1 := by simp [ch]

lemma ch_mul_neg (x : Fin 14) : ch x * ch (-x) = 1 := by
  rw [← ch_add, add_neg_cancel, ch_zero]

lemma ch_neg (x : Fin 14) : ch (-x) = (ch x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact ch_mul_neg x)

lemma ch_eq_one_iff (x : Fin 14) : ch x = 1 ↔ x = 0 := by
  constructor
  · intro h
    have hdvd : (14 : ℕ) ∣ x.val := (om_isPrimitiveRoot.pow_eq_one_iff_dvd x.val).1 h
    exact Fin.ext (Nat.eq_zero_of_dvd_of_lt hdvd x.isLt)
  · rintro rfl; exact ch_zero

/-! ### Arithmetic helpers in `Fin 14` -/

lemma fin_neg_mul_succ (k y : Fin 14) : -(k * (y + 1)) = -k + -(k * y) := by
  rw [mul_add, mul_one, neg_add, add_comm]

lemma fin_neg_mul_pred (k y : Fin 14) : -(k * (y - 1)) = k + -(k * y) := by
  rw [mul_sub, mul_one, neg_sub, sub_eq_add_neg]

lemma fin_mul_sub_eq (k x y : Fin 14) : k * x + -(k * y) = k * (x - y) := by
  rw [mul_sub, sub_eq_add_neg]

/-! ### Character orthogonality and Fourier inversion -/

/-- Orthogonality of characters: the character sum vanishes unless `d = 0`. -/
lemma sum_ch (d : Fin 14) : ∑ k : Fin 14, ch (k * d) = if d = 0 then 14 else 0 := by
  by_cases hd : d = 0
  · subst hd
    simp [ch_zero]
  · simp only [hd, if_false]
    set S := ∑ k : Fin 14, ch (k * d) with hS
    have key : ch d * S = S := by
      calc ch d * S = ∑ k : Fin 14, ch ((k + 1) * d) := by
            rw [hS, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [add_mul, one_mul, ch_add, mul_comm]
        _ = S := Fintype.sum_equiv (Equiv.addRight (1 : Fin 14)) _ _ (fun k => rfl)
    have hz : (ch d - 1) * S = 0 := by rw [sub_mul, one_mul, key, sub_self]
    rcases mul_eq_zero.1 hz with h | h
    · exact absurd ((ch_eq_one_iff d).1 (by linear_combination h)) hd
    · exact h

/-- The discrete Fourier coefficients of a function on `Fin 14`. -/
noncomputable def fcoeff (v : Fin 14 → ℂ) (k : Fin 14) : ℂ :=
  ∑ y : Fin 14, ch (-(k * y)) * v y

/-- Fourier inversion on `Fin 14`. -/
lemma fourier_inversion (v : Fin 14 → ℂ) (x : Fin 14) :
    ∑ k : Fin 14, ch (k * x) * fcoeff v k = 14 * v x := by
  have h1 : ∀ k : Fin 14, ch (k * x) * fcoeff v k
      = ∑ y : Fin 14, ch (k * (x - y)) * v y := by
    intro k
    rw [fcoeff, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [← mul_assoc, ← ch_add, fin_mul_sub_eq]
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ y : Fin 14, ∑ k : Fin 14, ch (k * (x - y)) * v y
      = (if x - y = 0 then (14 : ℂ) else 0) * v y := by
    intro y
    rw [← Finset.sum_mul, sum_ch]
  simp only [h2]
  have h3 : ∀ y : Fin 14, (if x - y = 0 then (14 : ℂ) else 0) * v y
      = if y = x then (14 : ℂ) * v y else 0 := by
    intro y
    by_cases h : y = x
    · subst h; simp
    · rw [if_neg h, if_neg (fun hc => h (by rw [sub_eq_zero] at hc; exact hc.symm)), zero_mul]
  simp only [h3]
  rw [Finset.sum_ite_eq' Finset.univ x (fun y => (14 : ℂ) * v y)]
  simp

/-- The eigenvalue attached to the character index `k`. -/
lemma ch_add_ch_neg (k : Fin 14) :
    ch k + ch (-k) = 2 * (Real.cos (2 * Real.pi * (k.val : ℝ) / 14) : ℂ) := by
  set t : ℝ := 2 * Real.pi * (k.val : ℝ) / 14 with ht
  have h1 : ch k = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [ch, om, ← Complex.exp_nat_mul]
    congr 1
    rw [ht]
    push_cast
    ring
  have h2 : ch (-k) = Complex.exp (-((t : ℂ) * Complex.I)) := by
    rw [ch_neg, h1, ← Complex.exp_neg]
  have h3 : Complex.cos (t : ℂ)
      = (Complex.exp ((t : ℂ) * Complex.I) + Complex.exp (-((t : ℂ) * Complex.I))) / 2 := by
    rw [Complex.cos]; ring_nf
  rw [h1, h2, Complex.ofReal_cos, h3]
  ring

lemma adj_mulVec (v : Fin 14 → ℂ) (x : Fin 14) :
    ((SimpleGraph.cycleGraph 14).adjMatrix ℂ).mulVec v x = v (x - 1) + v (x + 1) := by
  rw [SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.cycleGraph_neighborFinset,
    Finset.sum_pair (by revert x; decide)]

/-- **Hückel theory for the C₁₄ ring.**
A complex number `μ` is an eigenvalue of the adjacency matrix of the cycle graph `C₁₄`
if and only if `μ = 2 cos (2πk/14)` for some `k ∈ {0, …, 13}`. -/
theorem huckel_C14 (μ : ℂ) :
    (∃ v : Fin 14 → ℂ, v ≠ 0 ∧ ((SimpleGraph.cycleGraph 14).adjMatrix ℂ).mulVec v = μ • v) ↔
      ∃ k : ℕ, k < 14 ∧ μ = 2 * (Real.cos (2 * Real.pi * (k : ℝ) / 14) : ℂ) := by
  constructor
  · rintro ⟨v, hv, hA⟩
    have hcomp : ∀ x : Fin 14, v (x - 1) + v (x + 1) = μ * v x := by
      intro x
      have h := congrFun hA x
      rwa [adj_mulVec, Pi.smul_apply, smul_eq_mul] at h
    have hkey : ∀ k : Fin 14, (ch k + ch (-k)) * fcoeff v k = μ * fcoeff v k := by
      intro k
      have e1 : μ * fcoeff v k
          = (∑ y : Fin 14, ch (-(k * y)) * v (y - 1))
            + ∑ y : Fin 14, ch (-(k * y)) * v (y + 1) := by
        rw [fcoeff, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        linear_combination -(ch (-(k * y))) * hcomp y
      have e2 : ∑ y : Fin 14, ch (-(k * y)) * v (y - 1) = ch (-k) * fcoeff v k := by
        rw [← Fintype.sum_equiv (Equiv.addRight (1 : Fin 14))
          (fun y => ch (-(k * (y + 1))) * v y) (fun y => ch (-(k * y)) * v (y - 1))
          (fun y => by simp)]
        rw [fcoeff, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [← mul_assoc, ← ch_add, ← fin_neg_mul_succ]
      have e3 : ∑ y : Fin 14, ch (-(k * y)) * v (y + 1) = ch k * fcoeff v k := by
        rw [← Fintype.sum_equiv (Equiv.subRight (1 : Fin 14))
          (fun y => ch (-(k * (y - 1))) * v y) (fun y => ch (-(k * y)) * v (y + 1))
          (fun y => by simp)]
        rw [fcoeff, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [← mul_assoc, ← ch_add, ← fin_neg_mul_pred]
      rw [e1, e2, e3]
      ring
    have hex : ∃ k : Fin 14, fcoeff v k ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hv
      funext x
      have h := fourier_inversion v x
      simp only [hcon, mul_zero, Finset.sum_const_zero] at h
      rcases mul_eq_zero.1 h.symm with h' | h'
      · exact absurd h' (by norm_num)
      · simpa using h'
    obtain ⟨k, hk⟩ := hex
    refine ⟨k.val, k.isLt, ?_⟩
    have hmu : ch k + ch (-k) = μ := mul_right_cancel₀ hk (hkey k)
    rw [← hmu, ch_add_ch_neg]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨fun x => ch ((⟨k, hk⟩ : Fin 14) * x), ?_, ?_⟩
    · intro h
      have h0 : ch ((⟨k, hk⟩ : Fin 14) * 0) = 0 := congrFun h 0
      rw [mul_zero, ch_zero] at h0
      exact one_ne_zero h0
    · funext x
      rw [adj_mulVec, Pi.smul_apply, smul_eq_mul]
      set kk : Fin 14 := ⟨k, hk⟩ with hkk
      have h1 : kk * (x - 1) = kk * x + (-kk) := by rw [mul_sub, mul_one, sub_eq_add_neg]
      have h2 : kk * (x + 1) = kk * x + kk := by rw [mul_add, mul_one]
      have h3 : ch (-kk) + ch kk = 2 * (Real.cos (2 * Real.pi * (k : ℝ) / 14) : ℂ) := by
        rw [add_comm, ch_add_ch_neg]
      simp only [h1, h2, ch_add, ← mul_add, h3]
      ring

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

