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

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix Finset

/-- The primitive 12-th root of unity `exp(2πi/12)`. -/
noncomputable def w12 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 12)

/-- The character `ZMod 12 → ℂ`, `j ↦ ω^j`. -/
noncomputable def zeta12 (j : ZMod 12) : ℂ := w12 ^ j.val

/-- Adjacency matrix of the cycle graph `C₁₂`, indexed by `ZMod 12`. -/
def adjC12 : Matrix (ZMod 12) (ZMod 12) ℂ :=
  fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- The claimed Hückel eigenvalues `2 cos(2πk/12)`, `k = 0, …, 11`. -/
noncomputable def muC12 (k : ZMod 12) : ℝ := 2 * Real.cos (2 * Real.pi * k.val / 12)

lemma isPrimitiveRoot_w12 : IsPrimitiveRoot w12 12 :=
  Complex.isPrimitiveRoot_exp 12 (by norm_num)

lemma w12_pow_twelve : w12 ^ 12 = 1 := isPrimitiveRoot_w12.pow_eq_one

lemma w12_pow_mod (n : ℕ) : w12 ^ (n % 12) = w12 ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 12]
  rw [pow_add, pow_mul, w12_pow_twelve, one_pow, one_mul]

lemma zeta12_zero : zeta12 0 = 1 := by
  simp [zeta12]

lemma zeta12_add (a b : ZMod 12) : zeta12 (a + b) = zeta12 a * zeta12 b := by
  simp only [zeta12, ← pow_add]
  rw [ZMod.val_add, w12_pow_mod]

lemma zeta12_neg_mul (a : ZMod 12) : zeta12 a * zeta12 (-a) = 1 := by
  rw [← zeta12_add]; simp [zeta12_zero]

lemma zeta12_natCast_mul (n : ℕ) (m : ZMod 12) :
    zeta12 ((n : ZMod 12) * m) = zeta12 m ^ n := by
  induction n with
  | zero => simpa using zeta12_zero
  | succ n ih =>
      have h : ((n + 1 : ℕ) : ZMod 12) * m = (n : ZMod 12) * m + m := by push_cast; ring
      rw [h, zeta12_add, ih, pow_succ]

lemma zeta12_ne_one {m : ZMod 12} (hm : m ≠ 0) : zeta12 m ≠ 1 :=
  isPrimitiveRoot_w12.pow_ne_one_of_pos_of_lt ((ZMod.val_ne_zero m).mpr hm) (ZMod.val_lt m)

lemma zeta12_pow_twelve (m : ZMod 12) : zeta12 m ^ 12 = 1 := by
  rw [zeta12, ← pow_mul, mul_comm, pow_mul, w12_pow_twelve, one_pow]

lemma sum_univ_zmod12 (f : ZMod 12 → ℂ) :
    ∑ k : ZMod 12, f k = ∑ n ∈ Finset.range 12, f (n : ZMod 12) := by
  refine (Finset.sum_nbij' (fun n => ((n : ℕ) : ZMod 12)) (fun k => k.val) ?_ ?_ ?_ ?_ ?_)
  · intro n _; exact Finset.mem_univ _
  · intro k _; exact Finset.mem_range.mpr (ZMod.val_lt k)
  · intro n hn; simpa using ZMod.val_natCast_of_lt (Finset.mem_range.mp hn)
  · intro k _; exact ZMod.natCast_zmod_val k
  · intro n _; rfl

/-- Orthogonality of characters: the sum of `ζ^{km}` over `k` vanishes unless `m = 0`. -/
lemma sum_zeta12_mul (m : ZMod 12) :
    ∑ k : ZMod 12, zeta12 (k * m) = if m = 0 then 12 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp [zeta12_zero]
  · rw [if_neg hm, sum_univ_zmod12 (fun k => zeta12 (k * m))]
    have h : ∀ n ∈ Finset.range 12, zeta12 ((n : ZMod 12) * m) = zeta12 m ^ n := by
      intro n _; exact zeta12_natCast_mul n m
    rw [Finset.sum_congr rfl h, geom_sum_eq (zeta12_ne_one hm), zeta12_pow_twelve]
    simp

/-- The (unnormalised) discrete Fourier transform matrix. -/
noncomputable def dft12 : Matrix (ZMod 12) (ZMod 12) ℂ := fun j k => zeta12 (j * k)

/-- The inverse of the discrete Fourier transform matrix. -/
noncomputable def dft12inv : Matrix (ZMod 12) (ZMod 12) ℂ :=
  fun j k => (12 : ℂ)⁻¹ * zeta12 (-(j * k))

lemma dft12_mul_inv : dft12 * dft12inv = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have hstep : ∀ k : ZMod 12,
      dft12 j k * dft12inv k l = (12 : ℂ)⁻¹ * zeta12 (k * (j - l)) := by
    intro k
    have h : j * k + -(k * l) = k * (j - l) := by ring
    simp only [dft12, dft12inv]
    rw [← h, zeta12_add]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hstep k), ← Finset.mul_sum, sum_zeta12_mul]
  by_cases h : j = l
  · subst h; simp
  · have hjl : j - l ≠ 0 := sub_ne_zero.mpr h
    rw [if_neg hjl, Matrix.one_apply_ne h]
    ring

lemma dft12inv_mul : dft12inv * dft12 = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have hstep : ∀ k : ZMod 12,
      dft12inv j k * dft12 k l = (12 : ℂ)⁻¹ * zeta12 (k * (l - j)) := by
    intro k
    have h : -(j * k) + k * l = k * (l - j) := by ring
    simp only [dft12, dft12inv]
    rw [← h, zeta12_add]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hstep k), ← Finset.mul_sum, sum_zeta12_mul]
  by_cases h : j = l
  · subst h; simp
  · have hjl : l - j ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    rw [if_neg hjl, Matrix.one_apply_ne h]
    ring

/-- `ζ^k + ζ^{-k} = 2 cos(2πk/12)`. -/
lemma zeta12_add_neg (k : ZMod 12) : zeta12 k + zeta12 (-k) = (muC12 k : ℂ) := by
  have hθ : (k.val : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 12)
      = ((2 * Real.pi * k.val / 12 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hz : zeta12 k = Complex.exp (((2 * Real.pi * k.val / 12 : ℝ) : ℂ) * Complex.I) := by
    rw [zeta12, w12, ← Complex.exp_nat_mul, hθ]
  have hzinv : zeta12 (-k) = Complex.exp (-((2 * Real.pi * k.val / 12 : ℝ) : ℂ) * Complex.I) := by
    have h1 : (zeta12 k)⁻¹ = zeta12 (-k) := inv_eq_of_mul_eq_one_right (zeta12_neg_mul k)
    rw [← h1, hz, ← Complex.exp_neg]
    ring_nf
  rw [hz, hzinv, muC12]
  push_cast
  rw [eq_comm, Complex.two_cos]
  ring_nf

lemma adj_apply_split (i j : ZMod 12) :
    adjC12 i j = (if j = i + 1 then (1:ℂ) else 0) + (if j = i - 1 then (1:ℂ) else 0) := by
  have hne : i + 1 ≠ i - 1 := by
    intro h
    have h2 : (2 : ZMod 12) = 0 := by linear_combination h
    exact absurd h2 (by decide)
  by_cases h1 : j = i + 1
  · subst h1; simp [adjC12, hne]
  · by_cases h2 : j = i - 1
    · subst h2; simp [adjC12, h1]
    · simp [adjC12, h1, h2]

lemma adj_mul_dft : adjC12 * dft12 = dft12 * Matrix.diagonal (fun k => ((muC12 k : ℝ) : ℂ)) := by
  ext i l
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hL : ∑ j : ZMod 12, adjC12 i j * dft12 j l
      = zeta12 ((i + 1) * l) + zeta12 ((i - 1) * l) := by
    simp only [adj_apply_split, dft12, add_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (i+1) (fun j => zeta12 (j * l)),
      Finset.sum_ite_eq' Finset.univ (i-1) (fun j => zeta12 (j * l))]
    simp
  have hR : ∑ j : ZMod 12, dft12 i j * Matrix.diagonal (fun k => ((muC12 k : ℝ) : ℂ)) j l
      = zeta12 (i * l) * ((muC12 l : ℝ) : ℂ) := by
    simp [Matrix.diagonal, dft12]
  have e1 : zeta12 ((i + 1) * l) = zeta12 (i * l) * zeta12 l := by
    rw [show (i + 1) * l = i * l + l by ring, zeta12_add]
  have e2 : zeta12 ((i - 1) * l) = zeta12 (i * l) * zeta12 (-l) := by
    rw [show (i - 1) * l = i * l + -l by ring, zeta12_add]
  rw [hL, hR, ← zeta12_add_neg l, e1, e2]
  ring

/-- **Hückel theory for the cycle `C₁₂`.**  The characteristic polynomial of the adjacency
matrix of the cycle graph `C₁₂` factors as `∏_{k=0}^{11} (X - 2 cos(2πk/12))`; i.e. the
adjacency eigenvalues of `C₁₂` are exactly `2 cos(2πk/12)` for `k = 0, …, 11`. -/
theorem huckel_C12 :
    adjC12.charpoly =
      ∏ k : ZMod 12, (X - C ((2 * Real.cos (2 * Real.pi * k.val / 12) : ℝ) : ℂ)) := by
  classical
  set D : Matrix (ZMod 12) (ZMod 12) ℂ := Matrix.diagonal (fun k => ((muC12 k : ℝ) : ℂ)) with hD
  let U : (Matrix (ZMod 12) (ZMod 12) ℂ)ˣ :=
    ⟨dft12, dft12inv, dft12_mul_inv, dft12inv_mul⟩
  have hU : (U : Matrix (ZMod 12) (ZMod 12) ℂ) = dft12 := rfl
  have hUi : ((U⁻¹ : (Matrix (ZMod 12) (ZMod 12) ℂ)ˣ) : Matrix (ZMod 12) (ZMod 12) ℂ)
      = dft12inv := rfl
  have hA : adjC12
      = (U : Matrix (ZMod 12) (ZMod 12) ℂ) * D
        * ((U⁻¹ : (Matrix (ZMod 12) (ZMod 12) ℂ)ˣ) : Matrix (ZMod 12) (ZMod 12) ℂ) := by
    rw [hU, hUi, hD, ← adj_mul_dft, mul_assoc, dft12_mul_inv, mul_one]
  rw [hA, Matrix.charpoly_units_conj, hD, Matrix.charpoly_diagonal]
  rfl

end Chem

