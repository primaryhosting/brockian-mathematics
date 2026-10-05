/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators Real

namespace Chem

open Complex Finset

/-- A primitive 16-th root of unity. -/
noncomputable def w : ℂ := Complex.exp (2 * Real.pi * Complex.I / 16)

lemma w_prim : IsPrimitiveRoot w 16 := by
  have := Complex.isPrimitiveRoot_exp 16 (by norm_num)
  simpa [w] using this

lemma w_pow16 : w ^ 16 = 1 := w_prim.pow_eq_one

lemma w_pow_mod (n : ℕ) : w ^ (n % 16) = w ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 16, pow_add, pow_mul, w_pow16, one_pow, one_mul]

/-- The character `a ↦ w ^ a` on `ZMod 16`. -/
noncomputable def zeta (a : ZMod 16) : ℂ := w ^ a.val

lemma zeta_zero : zeta 0 = 1 := by simp [zeta]

lemma zeta_add (a b : ZMod 16) : zeta (a + b) = zeta a * zeta b := by
  simp only [zeta, ZMod.val_add, w_pow_mod, pow_add]

lemma zeta_ne_zero (a : ZMod 16) : zeta a ≠ 0 := by
  have : w ≠ 0 := by
    simp [w, Complex.exp_ne_zero]
  exact pow_ne_zero _ this

lemma zeta_neg (a : ZMod 16) : zeta (-a) = (zeta a)⁻¹ := by
  have h : zeta a * zeta (-a) = 1 := by
    rw [← zeta_add]; simp [zeta_zero]
  exact eq_inv_of_mul_eq_one_right h

lemma zeta_natCast_mul (n : ℕ) (b : ZMod 16) : zeta ((n : ZMod 16) * b) = zeta b ^ n := by
  induction n with
  | zero => simp [zeta_zero]
  | succ n ih =>
      push_cast
      rw [add_mul, one_mul, zeta_add, ih, pow_succ, mul_comm]

lemma zeta_eq_one_iff (a : ZMod 16) : zeta a = 1 ↔ a = 0 := by
  constructor
  · intro h
    by_contra hne
    have hval : a.val ≠ 0 := by
      intro h0
      apply hne
      rw [← ZMod.natCast_zmod_val a, h0]
      simp
    have hlt : a.val < 16 := ZMod.val_lt a
    exact (w_prim.pow_ne_one_of_pos_of_lt hval hlt) h
  · rintro rfl; exact zeta_zero

lemma zeta_sum (b : ZMod 16) : ∑ a : ZMod 16, zeta (a * b) = if b = 0 then 16 else 0 := by
  have key : ∑ a : ZMod 16, zeta (a * b) = ∑ m ∈ Finset.range 16, zeta b ^ m := by
    have h1 : ∀ a : ZMod 16, zeta (a * b) = zeta b ^ a.val := by
      intro a
      have hc : ((a.val : ℕ) : ZMod 16) = a := ZMod.natCast_zmod_val a
      conv_lhs => rw [← hc]
      rw [zeta_natCast_mul]
    simp only [h1]
    exact Fin.sum_univ_eq_sum_range (fun m => zeta b ^ m) 16
  rw [key]
  by_cases hb : b = 0
  · subst hb; simp [zeta_zero]
  · have hz : zeta b ≠ 1 := fun h => hb ((zeta_eq_one_iff b).1 h)
    rw [geom_sum_eq hz]
    have : zeta b ^ 16 = 1 := by
      have : ((16 : ℕ) : ZMod 16) = 0 := by decide
      have h2 := zeta_natCast_mul 16 b
      rw [this, zero_mul, zeta_zero] at h2
      exact h2.symm
    simp [this, hb]

/-- The adjacency matrix of the cycle graph `C₁₆`, indexed by `ZMod 16`. -/
def C16 : Matrix (ZMod 16) (ZMod 16) ℂ := fun i j => if i - j = 1 ∨ i - j = -1 then 1 else 0

lemma C16_mulVec (v : ZMod 16 → ℂ) (i : ZMod 16) :
    C16.mulVec v i = v (i - 1) + v (i + 1) := by
  have hne : (i - 1 : ZMod 16) ≠ i + 1 := by
    intro h
    have : (2 : ZMod 16) = 0 := by linear_combination -h
    exact absurd this (by decide)
  have hterm : ∀ j : ZMod 16, C16 i j * v j
      = if j ∈ ({i - 1, i + 1} : Finset (ZMod 16)) then v j else 0 := by
    intro j
    have h1 : (i - j = 1) ↔ j = i - 1 := by
      constructor <;> intro h <;> linear_combination -h
    have h2 : (i - j = -1) ↔ j = i + 1 := by
      constructor <;> intro h <;> linear_combination -h
    simp only [C16, h1, h2, Finset.mem_insert, Finset.mem_singleton]
    split <;> simp_all
  rw [Matrix.mulVec, dotProduct]
  simp only [hterm]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_pair hne]

lemma zeta_add_zeta_neg (k : ZMod 16) :
    zeta k + zeta (-k) = 2 * (Real.cos (2 * Real.pi * (k.val : ℝ) / 16) : ℂ) := by
  set θ : ℝ := 2 * Real.pi * (k.val : ℝ) / 16 with hθ
  have hzk : zeta k = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [zeta, w, ← Complex.exp_nat_mul]
    congr 1
    push_cast [hθ]
    ring
  have hzk' : zeta (-k) = Complex.exp (-(θ : ℂ) * Complex.I) := by
    rw [zeta_neg, hzk, ← Complex.exp_neg]
    congr 1; ring
  rw [hzk, hzk', ← Complex.two_cos, Complex.ofReal_cos]

/-- **Hückel theory for `C₁₆`**: the eigenvalues of the adjacency matrix of the cycle
graph `C₁₆` are exactly the numbers `2 cos (2πk/16)` for `k = 0, …, 15`. -/
theorem huckel_C16 (μ : ℂ) :
    (∃ v : ZMod 16 → ℂ, v ≠ 0 ∧ C16.mulVec v = μ • v) ↔
      ∃ k : Fin 16, μ = 2 * (Real.cos (2 * Real.pi * (k : ℕ) / 16) : ℂ) := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    obtain ⟨k, hk⟩ : ∃ k : ZMod 16, (∑ j : ZMod 16, v j * zeta (-(k * j))) ≠ 0 := by
      by_contra h
      push_neg at h
      apply hv0
      funext i
      have inv : ∑ k : ZMod 16, (∑ j : ZMod 16, v j * zeta (-(k * j))) * zeta (k * i)
          = 16 * v i := by
        have step : ∀ k : ZMod 16, (∑ j : ZMod 16, v j * zeta (-(k * j))) * zeta (k * i)
            = ∑ j : ZMod 16, v j * zeta (k * (i - j)) := by
          intro k
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [mul_assoc, ← zeta_add]
          congr 2
          ring
        simp only [step]
        rw [Finset.sum_comm]
        have : ∀ j : ZMod 16, ∑ k : ZMod 16, v j * zeta (k * (i - j))
            = if i - j = 0 then 16 * v j else 0 := by
          intro j
          rw [← Finset.mul_sum, zeta_sum]
          split <;> simp [mul_comm]
        simp only [this, sub_eq_zero]
        rw [Finset.sum_ite_eq]
        simp
      rw [show ∑ k : ZMod 16, (∑ j : ZMod 16, v j * zeta (-(k * j))) * zeta (k * i) = 0 by
        simp [h]] at inv
      have : (16 : ℂ) ≠ 0 := by norm_num
      simpa using (mul_eq_zero.1 inv.symm).resolve_left this
    have r1 : ∑ j : ZMod 16, v (j - 1) * zeta (-(k * j))
        = zeta (-k) * ∑ j : ZMod 16, v j * zeta (-(k * j)) := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.subRight (1 : ZMod 16)) _ _ ?_
      intro j
      have hz : zeta (-k) * zeta (-(k * (j - 1))) = zeta (-(k * j)) := by
        rw [← zeta_add]; congr 1; ring
      simp only [Equiv.subRight_apply]
      rw [← hz]; ring
    have r2 : ∑ j : ZMod 16, v (j + 1) * zeta (-(k * j))
        = zeta k * ∑ j : ZMod 16, v j * zeta (-(k * j)) := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.addRight (1 : ZMod 16)) _ _ ?_
      intro j
      have hz : zeta k * zeta (-(k * (j + 1))) = zeta (-(k * j)) := by
        rw [← zeta_add]; congr 1; ring
      show v (j + 1) * zeta (-(k * j)) = zeta k * (v (j + 1) * zeta (-(k * (j + 1))))
      rw [← hz]; ring
    have key : μ * (∑ j : ZMod 16, v j * zeta (-(k * j)))
        = (zeta k + zeta (-k)) * (∑ j : ZMod 16, v j * zeta (-(k * j))) := by
      have expand : μ * (∑ j : ZMod 16, v j * zeta (-(k * j)))
          = ∑ j : ZMod 16, (v (j - 1) + v (j + 1)) * zeta (-(k * j)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j _
        have hj : v (j - 1) + v (j + 1) = μ * v j := by
          have hcf := congrFun hv j
          rw [C16_mulVec] at hcf
          simpa using hcf
        rw [hj]; ring
      rw [expand]
      simp only [add_mul]
      rw [Finset.sum_add_distrib, r1, r2]
      ring
    have hμ : μ = zeta k + zeta (-k) := by
      have := mul_right_cancel₀ hk key
      exact this
    refine ⟨⟨k.val, ZMod.val_lt k⟩, ?_⟩
    rw [hμ, zeta_add_zeta_neg k]
  · rintro ⟨k, rfl⟩
    set K : ZMod 16 := ((k : ℕ) : ZMod 16) with hK
    have hKval : K.val = (k : ℕ) := by
      rw [hK, ZMod.val_natCast_of_lt k.isLt]
    refine ⟨fun i => zeta (K * i), ?_, ?_⟩
    · intro h
      have := congrFun h 0
      simp [zeta_zero] at this
    · funext i
      rw [C16_mulVec]
      have h1 : zeta (K * (i - 1)) = zeta (K * i) * zeta (-K) := by
        rw [← zeta_add]; congr 1; ring
      have h2 : zeta (K * (i + 1)) = zeta (K * i) * zeta K := by
        rw [← zeta_add]; congr 1; ring
      rw [h1, h2, Pi.smul_apply, smul_eq_mul]
      have := zeta_add_zeta_neg K
      rw [hKval] at this
      rw [← this]
      ring_nf

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

