import Mathlib
/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Complex Matrix

namespace Chem

/-- A primitive 13-th root of unity. -/
noncomputable def omega13 : ℂ := Complex.exp (2 * Real.pi * Complex.I / (13 : ℕ))

lemma isPrimitiveRoot_omega13 : IsPrimitiveRoot omega13 13 :=
  Complex.isPrimitiveRoot_exp 13 (by norm_num)

/-- The character `j ↦ ω^j` of `ZMod 13`. -/
noncomputable def e13 (j : ZMod 13) : ℂ := omega13 ^ j.val

lemma omega13_pow_13 : omega13 ^ 13 = 1 := isPrimitiveRoot_omega13.pow_eq_one

lemma omega13_pow_mod (n : ℕ) : omega13 ^ (n % 13) = omega13 ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 13]
  rw [pow_add, pow_mul, omega13_pow_13, one_pow, one_mul]

lemma e13_add (a b : ZMod 13) : e13 (a + b) = e13 a * e13 b := by
  simp only [e13, ZMod.val_add, omega13_pow_mod, pow_add]

@[simp] lemma e13_zero : e13 0 = 1 := by simp [e13]

lemma e13_ne_zero (a : ZMod 13) : e13 a ≠ 0 := by
  simp only [e13]
  exact pow_ne_zero _ (Complex.exp_ne_zero _)

lemma e13_neg (a : ZMod 13) : e13 (-a) = (e13 a)⁻¹ := by
  have h : e13 a * e13 (-a) = 1 := by rw [← e13_add]; simp
  exact (inv_eq_of_mul_eq_one_right h).symm

lemma e13_mul_neg (a : ZMod 13) : e13 a * e13 (-a) = 1 := by
  rw [← e13_add]; simp

lemma e13_ne_one {m : ZMod 13} (hm : m ≠ 0) : e13 m ≠ 1 := by
  have hlt : m.val < 13 := ZMod.val_lt m
  have hpos : m.val ≠ 0 := fun h0 => hm ((ZMod.val_eq_zero m).mp h0)
  exact isPrimitiveRoot_omega13.pow_ne_one_of_pos_of_lt hpos hlt

/-- Character orthogonality on `ZMod 13`. -/
lemma e13_sum (m : ZMod 13) : ∑ k : ZMod 13, e13 (k * m) = if m = 0 then 13 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp
  · simp only [hm, if_false]
    have h1 : e13 m * ∑ k : ZMod 13, e13 (k * m) = ∑ k : ZMod 13, e13 (k * m) := by
      rw [Finset.mul_sum]
      have hstep : ∀ k : ZMod 13, e13 m * e13 (k * m) = e13 ((k + 1) * m) := by
        intro k
        rw [add_mul, one_mul, e13_add, mul_comm]
      simp_rw [hstep]
      exact Fintype.sum_equiv (Equiv.addRight (1 : ZMod 13)) _ _ (fun k => rfl)
    have h2 : (e13 m - 1) * ∑ k : ZMod 13, e13 (k * m) = 0 := by
      rw [sub_mul, one_mul, h1, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (sub_eq_zero.mp h) (e13_ne_one hm)
    · exact h

/-- The adjacency matrix of the cycle graph `C₁₃`, with vertices indexed by `ZMod 13`. -/
def C13 : Matrix (ZMod 13) (ZMod 13) ℂ :=
  Matrix.of fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

lemma succ_ne_pred (i : ZMod 13) : (i + 1 : ZMod 13) ≠ i - 1 := by
  intro h
  have h2 : (2 : ZMod 13) = 0 := by linear_combination h
  exact absurd h2 (by decide)

lemma C13_mulVec (v : ZMod 13 → ℂ) (i : ZMod 13) :
    (C13 *ᵥ v) i = v (i + 1) + v (i - 1) := by
  have key : ∀ j : ZMod 13, (if j = i + 1 ∨ j = i - 1 then (1 : ℂ) else 0) * v j
      = (if j = i + 1 then v j else 0) + (if j = i - 1 then v j else 0) := by
    intro j
    rcases eq_or_ne j (i + 1) with h1 | h1
    · simp [h1, succ_ne_pred i]
    · rcases eq_or_ne j (i - 1) with h2 | h2
      · simp [h2, (succ_ne_pred i).symm]
      · simp [h1, h2]
  simp only [Matrix.mulVec, dotProduct, C13, Matrix.of_apply]
  simp_rw [key]
  rw [Finset.sum_add_distrib]
  simp

/-- The eigenvalue attached to the character index `k`. -/
noncomputable def huckelEigenvalue (k : ℕ) : ℝ := 2 * Real.cos (2 * Real.pi * k / 13)

lemma e13_eq_exp (k : ZMod 13) :
    e13 k = Complex.exp ((2 * Real.pi * (k.val : ℝ) / 13 : ℝ) * Complex.I) := by
  rw [e13, omega13, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma e13_add_inv (k : ZMod 13) :
    e13 k + (e13 k)⁻¹ = ((huckelEigenvalue k.val : ℝ) : ℂ) := by
  rw [e13_eq_exp, ← Complex.exp_neg, huckelEigenvalue]
  push_cast
  rw [Complex.cos, ← neg_mul]
  ring

/-- The Fourier characters are eigenvectors of the adjacency matrix. -/
lemma C13_mulVec_char (k : ZMod 13) :
    C13 *ᵥ (fun j => e13 (k * j))
      = ((huckelEigenvalue k.val : ℝ) : ℂ) • (fun j => e13 (k * j)) := by
  funext i
  rw [C13_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul]
  have h1 : e13 (k * (i + 1)) = e13 (k * i) * e13 k := by
    rw [mul_add, mul_one, e13_add]
  have h2 : e13 (k * (i - 1)) = e13 (k * i) * (e13 k)⁻¹ := by
    rw [mul_sub, mul_one, sub_eq_add_neg, e13_add, e13_neg]
  rw [h1, h2, ← e13_add_inv k]
  ring

/-- Fourier inversion on `ZMod 13`. -/
lemma fourier_inversion (v : ZMod 13 → ℂ) (j : ZMod 13) :
    ∑ k : ZMod 13, e13 (k * j) * (∑ l : ZMod 13, e13 (-(k * l)) * v l) = 13 * v j := by
  have step : ∀ k : ZMod 13, e13 (k * j) * (∑ l : ZMod 13, e13 (-(k * l)) * v l)
      = ∑ l : ZMod 13, e13 (k * (j - l)) * v l := by
    intro k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [← mul_assoc, ← e13_add]
    congr 2
    ring
  simp_rw [step]
  rw [Finset.sum_comm]
  have hfac : ∀ l : ZMod 13, (∑ k : ZMod 13, e13 (k * (j - l)) * v l)
      = (if j - l = 0 then (13 : ℂ) else 0) * v l := by
    intro l
    rw [← Finset.sum_mul, e13_sum]
  simp_rw [hfac]
  rw [Finset.sum_eq_single j]
  · simp
  · intro l _ hl
    have hjl : j - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hl)
    simp [hjl]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- **Hückel theory for the cycle `C₁₃`**: a complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₃` if and only if `μ = 2 cos (2πk/13)` for some
`k ∈ {0, 1, …, 12}`. -/
theorem huckel_C13 (μ : ℂ) :
    (∃ v : ZMod 13 → ℂ, v ≠ 0 ∧ C13 *ᵥ v = μ • v) ↔
      ∃ k : ℕ, k < 13 ∧ μ = ((2 * Real.cos (2 * Real.pi * k / 13) : ℝ) : ℂ) := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    obtain ⟨k, hk⟩ : ∃ k : ZMod 13, (∑ l : ZMod 13, e13 (-(k * l)) * v l) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hv0
      funext j
      have h := fourier_inversion v j
      simp only [hcon, mul_zero, Finset.sum_const_zero] at h
      have h13 : (13 : ℂ) * v j = 0 := h.symm
      simpa using (mul_eq_zero.mp h13).resolve_left (by norm_num)
    have hμv : ∀ j : ZMod 13, v (j + 1) + v (j - 1) = μ * v j := by
      intro j
      have h := congrFun hv j
      rw [C13_mulVec] at h
      simpa using h
    have hA : ∑ l : ZMod 13, e13 (-(k * l)) * v (l + 1)
        = e13 k * ∑ l : ZMod 13, e13 (-(k * l)) * v l := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.addRight (1 : ZMod 13)) _ _ (fun l => ?_)
      simp only [Equiv.coe_addRight]
      rw [show -(k * (l + 1)) = -(k * l) + -k by ring, e13_add]
      linear_combination (-(e13 (-(k * l)) * v (l + 1))) * e13_mul_neg k
    have hB : ∑ l : ZMod 13, e13 (-(k * l)) * v (l - 1)
        = e13 (-k) * ∑ l : ZMod 13, e13 (-(k * l)) * v l := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.subRight (1 : ZMod 13)) _ _ (fun l => ?_)
      simp only [Equiv.subRight_apply]
      rw [show -(k * (l - 1)) = -(k * l) + k by ring, e13_add]
      linear_combination (-(e13 (-(k * l)) * v (l - 1))) * e13_mul_neg k
    have hkey : μ * (∑ l : ZMod 13, e13 (-(k * l)) * v l)
        = (e13 k + e13 (-k)) * ∑ l : ZMod 13, e13 (-(k * l)) * v l := by
      calc μ * (∑ l : ZMod 13, e13 (-(k * l)) * v l)
          = ∑ l : ZMod 13, e13 (-(k * l)) * (v (l + 1) + v (l - 1)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun l _ => ?_)
            rw [hμv l]
            ring
        _ = (∑ l : ZMod 13, e13 (-(k * l)) * v (l + 1))
              + ∑ l : ZMod 13, e13 (-(k * l)) * v (l - 1) := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl (fun l _ => by ring)
        _ = (e13 k + e13 (-k)) * ∑ l : ZMod 13, e13 (-(k * l)) * v l := by
            rw [hA, hB]; ring
    have hμ : μ = e13 k + e13 (-k) := mul_right_cancel₀ hk hkey
    refine ⟨k.val, ZMod.val_lt k, ?_⟩
    rw [hμ, e13_neg, e13_add_inv k, huckelEigenvalue]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨fun j => e13 ((k : ZMod 13) * j), ?_, ?_⟩
    · intro h
      have hz := congrFun h 0
      simp at hz
    · have hval : ((k : ZMod 13)).val = k := ZMod.val_natCast_of_lt hk
      have h := C13_mulVec_char (k : ZMod 13)
      rw [hval, huckelEigenvalue] at h
      exact h

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

