import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header block is placed immediately after `import Mathlib`, since Lean 4 requires
-- `import` commands to come first in a file.)

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Finset

/-- A primitive 16-th root of unity. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 16)

lemma zeta_primitive : IsPrimitiveRoot zeta 16 := by
  have := Complex.isPrimitiveRoot_exp 16 (by norm_num)
  simpa [zeta] using this

lemma zeta_pow_16 : zeta ^ 16 = 1 := zeta_primitive.pow_eq_one

/-- The additive character `x ↦ exp(2πi x/16)` on `ZMod 16`. -/
noncomputable def ee (x : ZMod 16) : ℂ := zeta ^ x.val

lemma zeta_pow_mod (a : ℕ) : zeta ^ (a % 16) = zeta ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a 16]
  rw [pow_add, pow_mul, zeta_pow_16, one_pow, one_mul]

lemma ee_add (x y : ZMod 16) : ee (x + y) = ee x * ee y := by
  simp only [ee, ZMod.val_add, zeta_pow_mod, pow_add]

lemma ee_zero : ee 0 = 1 := by simp [ee]

lemma ee_ne_zero (x : ZMod 16) : ee x ≠ 0 := by
  simp [ee, zeta, Complex.exp_ne_zero]

lemma ee_natCast_mul (n : ℕ) (x : ZMod 16) : ee ((n : ZMod 16) * x) = ee x ^ n := by
  induction n with
  | zero => simp [ee_zero]
  | succ n ih =>
      have : ((n + 1 : ℕ) : ZMod 16) * x = (n : ZMod 16) * x + x := by push_cast; ring
      rw [this, ee_add, ih, pow_succ]

lemma ee_eq_one_iff (x : ZMod 16) : ee x = 1 ↔ x = 0 := by
  constructor
  · intro h
    have hdvd : (16 : ℕ) ∣ x.val := (zeta_primitive.pow_eq_one_iff_dvd x.val).1 h
    have hlt : x.val < 16 := ZMod.val_lt x
    exact (ZMod.val_eq_zero x).1 (Nat.eq_zero_of_dvd_of_lt hdvd hlt)
  · rintro rfl; exact ee_zero

lemma ee_pow_16 (x : ZMod 16) : ee x ^ 16 = 1 := by
  rw [ee, ← pow_mul, mul_comm, pow_mul, zeta_pow_16, one_pow]

lemma sum_zmod_eq_sum_range (f : ℕ → ℂ) :
    ∑ j : ZMod 16, f j.val = ∑ t ∈ Finset.range 16, f t := by
  rw [← Fin.sum_univ_eq_sum_range]
  rfl

/-- Orthogonality of the characters. -/
lemma sum_ee (d : ZMod 16) :
    ∑ j : ZMod 16, ee (j * d) = if d = 0 then 16 else 0 := by
  have hterm : ∀ j : ZMod 16, ee (j * d) = ee d ^ j.val := by
    intro j
    rw [← ee_natCast_mul j.val d, ZMod.natCast_zmod_val]
  rw [Finset.sum_congr rfl (fun j _ => hterm j),
    sum_zmod_eq_sum_range (fun t => ee d ^ t)]
  by_cases hd : d = 0
  · subst hd
    simp [ee_zero]
  · have hne : ee d ≠ 1 := fun h => hd ((ee_eq_one_iff d).1 h)
    rw [geom_sum_eq hne, ee_pow_16, if_neg hd]
    simp

/-- The adjacency matrix of the cycle graph `C₁₆`, indexed by `ZMod 16`. -/
def adjC16 : Matrix (ZMod 16) (ZMod 16) ℂ :=
  Matrix.of fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- The eigenvalue attached to `k`, namely `2·cos(2πk/16)`. -/
noncomputable def evC16 (k : ZMod 16) : ℂ := 2 * (Real.cos (2 * Real.pi * k.val / 16) : ℂ)

/-- The (unnormalized) discrete Fourier transform matrix. -/
noncomputable def dftP : Matrix (ZMod 16) (ZMod 16) ℂ := Matrix.of fun i k => ee (i * k)

/-- Its inverse. -/
noncomputable def dftQ : Matrix (ZMod 16) (ZMod 16) ℂ :=
  Matrix.of fun i k => (16 : ℂ)⁻¹ * ee (-(i * k))

lemma ee_eq_exp (k : ZMod 16) :
    ee k = Complex.exp (((2 * Real.pi * k.val / 16 : ℝ) : ℂ) * Complex.I) := by
  rw [ee, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma ee_neg (k : ZMod 16) : ee (-k) = (ee k)⁻¹ := by
  have h : ee k * ee (-k) = 1 := by rw [← ee_add, add_neg_cancel, ee_zero]
  field_simp [ee_ne_zero k]
  linear_combination h

lemma ee_add_ee_neg (k : ZMod 16) : ee k + ee (-k) = evC16 k := by
  rw [ee_neg, ee_eq_exp, evC16, ← Complex.exp_neg, Complex.ofReal_cos, Complex.two_cos, neg_mul]

lemma dftQ_mul_dftP : dftQ * dftP = 1 := by
  ext i k
  rw [Matrix.mul_apply]
  have hterm : ∀ j : ZMod 16, dftQ i j * dftP j k = (16 : ℂ)⁻¹ * ee (j * (k - i)) := by
    intro j
    have harg : -(i * j) + j * k = j * (k - i) := by ring
    simp only [dftQ, dftP, Matrix.of_apply, mul_assoc, ← ee_add, harg]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum, sum_ee, Matrix.one_apply]
  by_cases h : k = i
  · subst h; norm_num
  · rw [if_neg (sub_ne_zero.2 h), if_neg (Ne.symm h)]
    ring

lemma dftP_mul_dftQ : dftP * dftQ = 1 :=
  mul_eq_one_comm.2 dftQ_mul_dftP

lemma adj_mul_dftP : adjC16 * dftP = dftP * Matrix.diagonal evC16 := by
  have hne : ∀ i : ZMod 16, i + 1 ≠ i - 1 := by decide
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have hterm : ∀ j : ZMod 16, adjC16 i j * dftP j k =
      (if j = i + 1 then ee (j * k) else 0) + (if j = i - 1 then ee (j * k) else 0) := by
    intro j
    simp only [adjC16, dftP, Matrix.of_apply]
    rcases eq_or_ne j (i + 1) with h1 | h1
    · subst h1
      rw [if_pos (Or.inl rfl), if_pos rfl, if_neg (hne i), add_zero, one_mul]
    · rcases eq_or_ne j (i - 1) with h2 | h2
      · subst h2
        rw [if_pos (Or.inr rfl), if_neg h1, if_pos rfl, zero_add, one_mul]
      · rw [if_neg (not_or.2 ⟨h1, h2⟩), if_neg h1, if_neg h2, zero_mul, add_zero]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq' Finset.univ, Finset.mem_univ, if_true]
  have e1 : (i + 1) * k = i * k + k := by ring
  have e2 : (i - 1) * k = i * k + (-k) := by ring
  simp only [dftP, Matrix.of_apply]
  rw [e1, e2, ee_add, ee_add, ← mul_add, ee_add_ee_neg]

/-- **Hückel theory for the C₁₆ annulene ring.**
A complex number `μ` is an eigenvalue of the adjacency matrix of the cycle graph `C₁₆`
if and only if `μ = 2 cos (2πk/16)` for some `k ∈ {0, …, 15}`. -/
theorem huckel_C16 (μ : ℂ) :
    (∃ v : ZMod 16 → ℂ, v ≠ 0 ∧ adjC16.mulVec v = μ • v) ↔
      ∃ k : ZMod 16, μ = 2 * (Real.cos (2 * Real.pi * k.val / 16) : ℂ) := by
  constructor
  · rintro ⟨v, hv, hAv⟩
    set u : ZMod 16 → ℂ := dftQ.mulVec v with hu
    have hPu : dftP.mulVec u = v := by
      rw [hu, Matrix.mulVec_mulVec, dftP_mul_dftQ, Matrix.one_mulVec]
    have hune : u ≠ 0 := by
      intro h
      apply hv
      rw [← hPu, h, Matrix.mulVec_zero]
    have key : (Matrix.diagonal evC16).mulVec u = μ • u := by
      have h1 : dftP.mulVec ((Matrix.diagonal evC16).mulVec u) = dftP.mulVec (μ • u) := by
        rw [Matrix.mulVec_mulVec, ← adj_mul_dftP, ← Matrix.mulVec_mulVec, hPu, hAv,
          Matrix.mulVec_smul, hPu]
      have h2 := congrArg (fun w => dftQ.mulVec w) h1
      simpa [Matrix.mulVec_mulVec, ← mul_assoc, dftQ_mul_dftP, Matrix.one_mulVec] using h2
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hune
    refine ⟨k, ?_⟩
    have := congrFun key k
    rw [Matrix.mulVec_diagonal] at this
    have hmu : evC16 k = μ := by
      field_simp at this
      rcases mul_eq_mul_right_iff.1 this with h | h
      · exact h
      · exact absurd h hk
    rw [← hmu, evC16]
  · rintro ⟨k, rfl⟩
    refine ⟨fun i => dftP i k, ?_, ?_⟩
    · intro h
      have h0 := congrFun h 0
      simp only [dftP, Matrix.of_apply, Pi.zero_apply] at h0
      exact ee_ne_zero _ h0
    · funext i
      have h := congrFun (congrFun adj_mul_dftP i) k
      rw [Matrix.mul_apply, Matrix.mul_diagonal] at h
      simpa [Matrix.mulVec, dotProduct, evC16, mul_comm] using h

end Chem

