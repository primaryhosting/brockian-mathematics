import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Real Matrix Finset

/-- A primitive 18-th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 18)

lemma om_prim : IsPrimitiveRoot om 18 := by
  simpa [om] using Complex.isPrimitiveRoot_exp 18 (by norm_num)

lemma om_pow_18 : om ^ 18 = 1 := om_prim.pow_eq_one

lemma om_pow_nat (m : ℕ) :
    om ^ m = Complex.exp (((2 * Real.pi * m / 18 : ℝ) : ℂ) * Complex.I) := by
  rw [om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The standard additive character of `ZMod 18` with values in `ℂ`. -/
noncomputable def ee (a : ZMod 18) : ℂ := om ^ a.val

lemma ee_add (a b : ZMod 18) : ee (a + b) = ee a * ee b := by
  unfold ee
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.div_add_mod (a.val + b.val) 18]
  rw [pow_add, pow_mul, om_pow_18, one_pow, one_mul]

lemma ee_zero : ee 0 = 1 := by simp [ee]

lemma ee_ne_zero (a : ZMod 18) : ee a ≠ 0 := by
  have : ee a * ee (-a) = 1 := by rw [← ee_add, add_neg_cancel, ee_zero]
  intro h
  rw [h, zero_mul] at this
  exact zero_ne_one this

lemma ee_nsmul (c : ZMod 18) (n : ℕ) : ee (n • c) = ee c ^ n := by
  induction n with
  | zero => simp [ee_zero]
  | succ n ih => rw [succ_nsmul, ee_add, ih, pow_succ]

lemma ee_mul (j c : ZMod 18) : ee (j * c) = ee c ^ j.val := by
  rw [← ee_nsmul, nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id]

lemma ee_pow_18 (c : ZMod 18) : ee c ^ 18 = 1 := by
  rw [← ee_nsmul, nsmul_eq_mul, show ((18 : ℕ) : ZMod 18) = 0 from ZMod.natCast_self 18,
    zero_mul, ee_zero]

lemma ee_ne_one (c : ZMod 18) (hc : c ≠ 0) : ee c ≠ 1 := by
  have h1 : c.val ≠ 0 := fun h => hc ((ZMod.val_eq_zero c).mp h)
  exact om_prim.pow_ne_one_of_pos_of_lt h1 (ZMod.val_lt c)

/-- Orthogonality relation for the character `ee`. -/
lemma ee_sum (c : ZMod 18) : ∑ j : ZMod 18, ee (j * c) = if c = 0 then 18 else 0 := by
  have hstep : ∑ j : ZMod 18, ee (j * c) = ∑ i ∈ Finset.range 18, (ee c) ^ i := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun x _ => ee_mul x c)
  rw [hstep]
  by_cases hc : c = 0
  · simp [hc, ee_zero]
  · rw [if_neg hc, geom_sum_eq (ee_ne_one c hc), ee_pow_18, sub_self, zero_div]

/-- `ee k + ee (-k) = 2 cos (2πk/18)`. -/
lemma ee_add_neg (k : ZMod 18) :
    ee k + ee (-k) = ((2 * Real.cos (2 * Real.pi * k.val / 18) : ℝ) : ℂ) := by
  set t : ℝ := 2 * Real.pi * k.val / 18 with ht
  have h1 : ee k = Complex.exp ((t : ℂ) * Complex.I) := om_pow_nat k.val
  have hmul : ee k * ee (-k) = 1 := by rw [← ee_add, add_neg_cancel, ee_zero]
  have h2 : ee (-k) = Complex.exp (-((t : ℂ) * Complex.I)) := by
    have hne : ee k ≠ 0 := ee_ne_zero k
    field_simp [h1, Complex.exp_neg] at hmul ⊢
    rw [← hmul, h1]
  rw [h1, h2]
  have := Complex.cos_eq_exp_add_exp_neg_div_two ((t : ℂ))
  push_cast
  rw [← Complex.ofReal_cos]
  push_cast
  rw [this]
  ring

/-- Adjacency matrix of the cycle graph `C₁₈`, with vertices indexed by `ZMod 18`. -/
def C18adj : Matrix (ZMod 18) (ZMod 18) ℂ :=
  Matrix.of fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- The discrete Fourier matrix. -/
noncomputable def U : Matrix (ZMod 18) (ZMod 18) ℂ := Matrix.of fun j k => ee (j * k)

/-- The inverse of the discrete Fourier matrix. -/
noncomputable def V : Matrix (ZMod 18) (ZMod 18) ℂ :=
  Matrix.of fun k l => (18 : ℂ)⁻¹ * ee (-(k * l))

/-- The diagonal matrix of Hückel eigenvalues. -/
noncomputable def Dg : Matrix (ZMod 18) (ZMod 18) ℂ :=
  Matrix.diagonal fun k => ((2 * Real.cos (2 * Real.pi * k.val / 18) : ℝ) : ℂ)

lemma UV : U * V = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have h : ∀ k : ZMod 18, U j k * V k l = (18 : ℂ)⁻¹ * ee (k * (j - l)) := by
    intro k
    simp only [U, V, Matrix.of_apply]
    rw [show k * (j - l) = j * k + -(k * l) by ring, ee_add]
    ring
  rw [Finset.sum_congr rfl (fun k _ => h k), ← Finset.mul_sum, ee_sum]
  by_cases hjl : j = l
  · simp [hjl, Matrix.one_apply]
  · have : j - l ≠ 0 := sub_ne_zero_of_ne hjl
    simp [this, Matrix.one_apply, hjl]

lemma VU : V * U = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have h : ∀ k : ZMod 18, V j k * U k l = (18 : ℂ)⁻¹ * ee (k * (l - j)) := by
    intro k
    simp only [U, V, Matrix.of_apply]
    rw [show k * (l - j) = -(j * k) + k * l by ring, ee_add]
    ring
  rw [Finset.sum_congr rfl (fun k _ => h k), ← Finset.mul_sum, ee_sum]
  by_cases hjl : j = l
  · simp [hjl, Matrix.one_apply]
  · have : l - j ≠ 0 := sub_ne_zero_of_ne (Ne.symm hjl)
    simp [this, Matrix.one_apply, hjl]

lemma AU : C18adj * U = U * Dg := by
  ext j k
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hne : j + 1 ≠ j - 1 := by
    intro h
    have : (2 : ZMod 18) = 0 := by linear_combination h
    exact absurd this (by decide)
  have hsplit : ∀ i : ZMod 18, C18adj j i * U i k
      = (if i = j + 1 then ee (i * k) else 0) + (if i = j - 1 then ee (i * k) else 0) := by
    intro i
    simp only [C18adj, U, Matrix.of_apply]
    by_cases h1 : i = j + 1
    · rw [if_pos h1, if_pos (Or.inl h1), if_neg (by rw [h1]; exact hne)]
      ring
    · by_cases h2 : i = j - 1
      · rw [if_neg h1, if_pos h2, if_pos (Or.inr h2)]
        ring
      · rw [if_neg h1, if_neg h2, if_neg (by tauto)]
        ring
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (j + 1) (fun i => ee (i * k)),
    Finset.sum_ite_eq' Finset.univ (j - 1) (fun i => ee (i * k))]
  simp only [Finset.mem_univ, if_true]
  rw [Dg, Matrix.diagonal_apply]
  have hsum : ∑ l : ZMod 18, U j l * (if l = k then ((2 * Real.cos (2 * Real.pi * k.val / 18) : ℝ) : ℂ) else 0)
      = U j k * ((2 * Real.cos (2 * Real.pi * k.val / 18) : ℝ) : ℂ) := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ k) h
  rw [show (∑ l : ZMod 18, U j l * (if k = l then ((2 * Real.cos (2 * Real.pi * k.val / 18) : ℝ) : ℂ) else 0))
      = ∑ l : ZMod 18, U j l * (if l = k then ((2 * Real.cos (2 * Real.pi * k.val / 18) : ℝ) : ℂ) else 0) from
      Finset.sum_congr rfl (fun l _ => by by_cases h : l = k <;> simp [h, eq_comm]), hsum]
  simp only [U, Matrix.of_apply]
  rw [show (j + 1) * k = j * k + k by ring, show (j - 1) * k = j * k + -k by ring,
    ee_add, ee_add, ← mul_add, ee_add_neg]

/-- **Hückel theory for the cycle `C₁₈`.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₈` if and only if `μ = 2 cos (2πk/18)` for some
`k ∈ {0, …, 17}`. -/
theorem huckel_C18 (mu : ℂ) :
    (∃ v : ZMod 18 → ℂ, v ≠ 0 ∧ C18adj.mulVec v = mu • v) ↔
      ∃ k : Fin 18, mu = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 18) : ℝ) : ℂ) := by
  constructor
  · rintro ⟨v, hv, hAv⟩
    refine ?_
    set w := V.mulVec v with hw
    have hUw : U.mulVec w = v := by
      rw [hw, Matrix.mulVec_mulVec, UV, Matrix.one_mulVec]
    have hwne : w ≠ 0 := by
      intro h
      rw [h] at hUw
      simp at hUw
      exact hv hUw.symm
    have hDw : Dg.mulVec w = mu • w := by
      have : Dg = V * (C18adj * U) := by rw [AU, ← Matrix.mul_assoc, VU, Matrix.one_mul]
      rw [this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hUw, hAv,
        Matrix.mulVec_smul]
    obtain ⟨k, hk⟩ : ∃ k : ZMod 18, w k ≠ 0 := by
      by_contra h
      push_neg at h
      exact hwne (funext h)
    have := congrFun hDw k
    rw [Dg, Matrix.mulVec_diagonal] at this
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have hmu : mu = ((2 * Real.cos (2 * Real.pi * k.val / 18) : ℝ) : ℂ) := by
      field_simp at this
      rcases this with h | h
      · exact h.symm
      · exact absurd h hk
    exact ⟨⟨k.val, ZMod.val_lt k⟩, hmu⟩
  · rintro ⟨k, hk⟩
    set kz : ZMod 18 := ((k : ℕ) : ZMod 18) with hkz
    have hval : kz.val = (k : ℕ) := ZMod.val_natCast_of_lt k.isLt
    refine ⟨U.mulVec (Pi.single kz 1), ?_, ?_⟩
    · intro h
      have h0 := congrFun h 0
      rw [Matrix.mulVec, Matrix.dotProduct] at h0
      simp only [Pi.zero_apply] at h0
      rw [Finset.sum_eq_single kz] at h0
      · simp only [U, Matrix.of_apply, Pi.single_eq_same, mul_one] at h0
        rw [zero_mul, ee_zero] at h0
        exact one_ne_zero h0
      · intro b _ hb; simp [Pi.single_eq_of_ne hb]
      · intro h; exact absurd (Finset.mem_univ kz) h
    · rw [Matrix.mulVec_mulVec, AU, ← Matrix.mulVec_mulVec]
      have : Dg.mulVec (Pi.single kz 1) = mu • Pi.single kz (1 : ℂ) := by
        funext i
        rw [Dg, Matrix.mulVec_diagonal]
        simp only [Pi.smul_apply, smul_eq_mul]
        by_cases hi : i = kz
        · subst hi
          rw [Pi.single_eq_same, hk, hval]
        · rw [Pi.single_eq_of_ne hi, mul_zero, mul_zero]
      rw [this, Matrix.mulVec_smul]

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

