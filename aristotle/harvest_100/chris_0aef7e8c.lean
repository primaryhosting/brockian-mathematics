/-
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Matrix Finset

/-- The graph Laplacian of the cycle graph `C n`, as the `n × n` circulant matrix with `2` on the
diagonal and `-1` on the two cyclic off-diagonals. -/
noncomputable def cycleLaplacian (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j =>
    if i = j then 2 else if (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val then -1 else 0

/-- Sanity check: for `n = 3` this is the usual Laplacian of the triangle. -/
example : cycleLaplacian 3 = !![2, -1, -1; -1, 2, -1; -1, -1, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [cycleLaplacian]

/-- Sanity check: for `n = 4` this is the usual Laplacian of the 4-cycle. -/
example : cycleLaplacian 4 = !![2, -1, 0, -1; -1, 2, -1, 0; 0, -1, 2, -1; -1, 0, -1, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [cycleLaplacian]

section
variable (n : ℕ) [NeZero n]

/-- The identification of `Fin n` with `ZMod n`. -/
def finZModEquiv : Fin n ≃ ZMod n where
  toFun i := (i.val : ZMod n)
  invFun a := ⟨a.val, a.val_lt⟩
  left_inv i := by ext; simp [ZMod.val_natCast_of_lt i.isLt]
  right_inv a := by simp [ZMod.natCast_val]

/-- The cycle Laplacian, indexed by `ZMod n`. -/
noncomputable def cycleLaplacianZ : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.of fun i j => if i = j then 2 else if i - j = 1 ∨ i - j = -1 then -1 else 0

/-- The discrete Fourier matrix, whose columns are the eigenvectors
`v k (j) = exp (2 π I k j / n)`. -/
noncomputable def dftMatrix : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.of fun j k => ZMod.stdAddChar (j * k)

/-- The inverse of `dftMatrix`. -/
noncomputable def invDftMatrix : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.of fun j k => (n : ℂ)⁻¹ * ZMod.stdAddChar (-(j * k))

/-- The eigenvalue attached to the `k`-th Fourier mode. -/
noncomputable def cycleEig (k : ZMod n) : ℂ :=
  2 - 2 * Real.cos (2 * Real.pi * k.val / n)

end

variable {n : ℕ} [NeZero n]

lemma stdAddChar_sum (t : ZMod n) :
    ∑ i : ZMod n, ZMod.stdAddChar (t * i) = if t = 0 then (n : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar n h)

lemma dft_mul_invDft : dftMatrix n * invDftMatrix n = 1 := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  ext j l
  rw [Matrix.mul_apply]
  have key : ∀ k : ZMod n, dftMatrix n j k * invDftMatrix n k l
      = (n : ℂ)⁻¹ * ZMod.stdAddChar ((j - l) * k) := by
    intro k
    simp only [dftMatrix, invDftMatrix, Matrix.of_apply]
    rw [show (j - l) * k = j * k + (-(k * l)) by ring, AddChar.map_add_eq_mul]
    ring
  simp only [key, ← Finset.mul_sum, stdAddChar_sum]
  by_cases h : j = l
  · subst h; simp [inv_mul_cancel₀ hn0]
  · simp [h, sub_eq_zero]

lemma invDft_mul_dft : invDftMatrix n * dftMatrix n = 1 := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  ext j l
  rw [Matrix.mul_apply]
  have key : ∀ k : ZMod n, invDftMatrix n j k * dftMatrix n k l
      = (n : ℂ)⁻¹ * ZMod.stdAddChar ((l - j) * k) := by
    intro k
    simp only [dftMatrix, invDftMatrix, Matrix.of_apply]
    rw [show (l - j) * k = (-(j * k)) + k * l by ring, AddChar.map_add_eq_mul]
    ring
  simp only [key, ← Finset.mul_sum, stdAddChar_sum]
  by_cases h : j = l
  · subst h; simp [inv_mul_cancel₀ hn0]
  · simp [h, sub_eq_zero, Ne.symm h]

lemma stdAddChar_add_neg (k : ZMod n) :
    ZMod.stdAddChar k + ZMod.stdAddChar (-k) = 2 * Real.cos (2 * Real.pi * k.val / n) := by
  have hk : (ZMod.stdAddChar k : ℂ) = Complex.exp (2 * Real.pi * Complex.I * k.val / n) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  have hneg : (ZMod.stdAddChar (-k) : ℂ)
      = Complex.exp (2 * Real.pi * Complex.I * ((-(k.val : ℤ) : ℤ) : ℂ) / n) := by
    rw [← ZMod.stdAddChar_coe]
    congr 1
    push_cast
    simp [ZMod.natCast_val]
  rw [hk, hneg]
  set t : ℝ := 2 * Real.pi * k.val / n with ht
  have e1 : (2 : ℂ) * Real.pi * Complex.I * k.val / n = (t : ℂ) * Complex.I := by
    rw [ht]; push_cast; ring
  have e2 : (2 : ℂ) * Real.pi * Complex.I * ((-(k.val : ℤ) : ℤ) : ℂ) / n
      = -((t : ℂ) * Complex.I) := by
    rw [ht]; push_cast; ring
  rw [e1, e2, Complex.exp_mul_I, ← neg_mul, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_cos]
  ring

lemma laplacianZ_mul_dft (hn : 3 ≤ n) :
    cycleLaplacianZ n * dftMatrix n = dftMatrix n * Matrix.diagonal (cycleEig n) := by
  have h1 : (1 : ZMod n) ≠ 0 := by
    intro h
    have hd : (n : ℕ) ∣ 1 := (ZMod.natCast_eq_zero_iff 1 n).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd one_pos hd
    omega
  have h2 : (2 : ZMod n) ≠ 0 := by
    intro h
    have hd : (n : ℕ) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd two_pos hd
    omega
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have hA : ¬ ((i : ZMod n) = i - 1) := fun h => h1 (by linear_combination h)
  have hB : ¬ ((i : ZMod n) = i + 1) := fun h => h1 (by linear_combination -h)
  have hD : ¬ ((i : ZMod n) - 1 = i + 1) := fun h => h2 (by linear_combination -h)
  have hA2 : ¬ ((i : ZMod n) - 1 = i) := fun h => hA h.symm
  have hB2 : ¬ ((i : ZMod n) + 1 = i) := fun h => hB h.symm
  have hD2 : ¬ ((i : ZMod n) + 1 = i - 1) := fun h => hD h.symm
  have hs1 : (i : ZMod n) - (i - 1) = 1 := by ring
  have hs2 : (i : ZMod n) - (i + 1) = -1 := by ring
  have hne : (-1 : ZMod n) ≠ 1 := fun h => h2 (by linear_combination -h)
  have hrow : ∀ j : ZMod n, cycleLaplacianZ n i j * dftMatrix n j k
      = (if j = i then 2 * ZMod.stdAddChar (i * k) else 0)
        + (if j = i - 1 then -ZMod.stdAddChar ((i - 1) * k) else 0)
        + (if j = i + 1 then -ZMod.stdAddChar ((i + 1) * k) else 0) := by
    intro j
    simp only [cycleLaplacianZ, dftMatrix, Matrix.of_apply]
    by_cases hji : j = i
    · simp [hji, hA, hB]
    · by_cases hj1 : j = i - 1
      · simp [hj1, hA, hA2, hD, hs1]
      · by_cases hj2 : j = i + 1
        · simp [hj2, hB, hB2, hD2, hs2, hne]
        · have hc1 : ¬ ((i : ZMod n) - j = 1) := fun h => hj1 (by linear_combination -h)
          have hc2 : ¬ ((i : ZMod n) - j = -1) := fun h => hj2 (by linear_combination -h)
          simp [hji, hj1, hj2, hc1, hc2, Ne.symm hji]
  simp only [hrow, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have e1 : ZMod.stdAddChar ((i - 1) * k)
      = ZMod.stdAddChar (i * k) * ZMod.stdAddChar (-k) := by
    rw [← AddChar.map_add_eq_mul]; ring_nf
  have e2 : ZMod.stdAddChar ((i + 1) * k)
      = ZMod.stdAddChar (i * k) * ZMod.stdAddChar k := by
    rw [← AddChar.map_add_eq_mul]; ring_nf
  have e3 := stdAddChar_add_neg (n := n) k
  simp only [dftMatrix, Matrix.of_apply, cycleEig]
  rw [e1, e2]
  linear_combination -(ZMod.stdAddChar (i * k) : ℂ) * e3

lemma range_cycleEig :
    Set.range (cycleEig n) =
      (fun k : ℕ => ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ)) ''
        (Finset.range n : Set ℕ) := by
  ext x
  simp only [Set.mem_range, Set.mem_image, Finset.coe_range, Set.mem_Iio]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k.val, k.val_lt, by simp [cycleEig]⟩
  · rintro ⟨m, hm, rfl⟩
    refine ⟨(m : ZMod n), ?_⟩
    rw [cycleEig, ZMod.val_natCast_of_lt hm]
    push_cast
    ring

lemma succ_val_iff (a b : ZMod n) : (a.val + 1) % n = b.val ↔ a + 1 = b := by
  constructor
  · intro h
    have : ((a.val + 1 : ℕ) : ZMod n) = ((b.val : ℕ) : ZMod n) := by
      rw [ZMod.natCast_eq_natCast_iff', h, Nat.mod_eq_of_lt b.val_lt]
    simpa [ZMod.natCast_val, ZMod.natCast_zmod_val] using this
  · intro h
    have : ((a.val + 1 : ℕ) : ZMod n) = ((b.val : ℕ) : ZMod n) := by
      push_cast
      simpa [ZMod.natCast_val, ZMod.natCast_zmod_val] using h
    rw [ZMod.natCast_eq_natCast_iff'] at this
    rwa [Nat.mod_eq_of_lt b.val_lt] at this

omit [NeZero n] in
lemma add_one_iff_sub_eq_neg_one (a b : ZMod n) : a + 1 = b ↔ a - b = -1 := by
  constructor
  · rintro rfl; ring
  · intro h; linear_combination h

lemma cycleLaplacian_eq_reindex :
    cycleLaplacian n
      = Matrix.reindex (finZModEquiv n).symm (finZModEquiv n).symm (cycleLaplacianZ n) := by
  ext i j
  have hi : ((i.val : ZMod n)).val = i.val := ZMod.val_natCast_of_lt i.isLt
  have hj : ((j.val : ZMod n)).val = j.val := ZMod.val_natCast_of_lt j.isLt
  have heq : ((i.val : ZMod n) = (j.val : ZMod n)) ↔ i = j := by
    constructor
    · intro h
      have := congrArg ZMod.val h
      rw [hi, hj] at this
      exact Fin.ext this
    · rintro rfl; rfl
  have h1 : (i.val + 1) % n = j.val ↔ (i.val : ZMod n) - (j.val : ZMod n) = -1 := by
    have h := succ_val_iff ((i.val : ZMod n)) ((j.val : ZMod n))
    rw [hi, hj, add_one_iff_sub_eq_neg_one] at h
    exact h
  have h2 : (j.val + 1) % n = i.val ↔ (i.val : ZMod n) - (j.val : ZMod n) = 1 := by
    have h := succ_val_iff ((j.val : ZMod n)) ((i.val : ZMod n))
    rw [hi, hj, add_one_iff_sub_eq_neg_one] at h
    rw [h]
    constructor
    · intro hh; linear_combination -hh
    · intro hh; linear_combination -hh
  simp only [cycleLaplacian, cycleLaplacianZ, Matrix.of_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm, finZModEquiv, Equiv.coe_fn_mk]
  by_cases hij : i = j
  · subst hij; simp
  · have hij' : ((i.val : ZMod n)) ≠ (j.val : ZMod n) := fun h => hij (heq.mp h)
    rw [if_neg hij, if_neg hij']
    by_cases hc : (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val
    · rw [if_pos hc, if_pos]
      rcases hc with h | h
      · exact Or.inr (h1.mp h)
      · exact Or.inl (h2.mp h)
    · rw [if_neg hc, if_neg]
      rintro (h | h)
      · exact hc (Or.inr (h2.mpr h))
      · exact hc (Or.inl (h1.mpr h))

/-- **Spectrum of the cycle Laplacian.** For `n ≥ 3`, the eigenvalues of the graph Laplacian of
the cycle `C n` are exactly `2 - 2 cos (2 π k / n)` for `k = 0, …, n - 1`. -/
theorem cycle_laplacian_spectrum (n : ℕ) (hn : 3 ≤ n) :
    spectrum ℂ (cycleLaplacian n) =
      (fun k : ℕ => ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ)) ''
        (Finset.range n : Set ℕ) := by
  haveI : NeZero n := ⟨by omega⟩
  have hre : spectrum ℂ (cycleLaplacian n) = spectrum ℂ (cycleLaplacianZ n) := by
    rw [cycleLaplacian_eq_reindex (n := n)]
    exact AlgEquiv.spectrum_eq (Matrix.reindexAlgEquiv ℂ ℂ (finZModEquiv n).symm)
      (cycleLaplacianZ n)
  set F : (Matrix (ZMod n) (ZMod n) ℂ)ˣ :=
    ⟨dftMatrix n, invDftMatrix n, dft_mul_invDft, invDft_mul_dft⟩
  have hFval : (F : Matrix (ZMod n) (ZMod n) ℂ) = dftMatrix n := rfl
  have hL : cycleLaplacianZ n
      = (F : Matrix (ZMod n) (ZMod n) ℂ) * Matrix.diagonal (cycleEig n)
        * ((F⁻¹ : (Matrix (ZMod n) (ZMod n) ℂ)ˣ) : Matrix (ZMod n) (ZMod n) ℂ) := by
    have h := laplacianZ_mul_dft (n := n) hn
    have hmul : (F : Matrix (ZMod n) (ZMod n) ℂ)
        * ((F⁻¹ : (Matrix (ZMod n) (ZMod n) ℂ)ˣ) : Matrix (ZMod n) (ZMod n) ℂ) = 1 :=
      F.mul_inv
    calc cycleLaplacianZ n
        = cycleLaplacianZ n * ((F : Matrix (ZMod n) (ZMod n) ℂ)
            * ((F⁻¹ : (Matrix (ZMod n) (ZMod n) ℂ)ˣ) : Matrix (ZMod n) (ZMod n) ℂ)) := by
          rw [hmul, mul_one]
      _ = (cycleLaplacianZ n * dftMatrix n)
            * ((F⁻¹ : (Matrix (ZMod n) (ZMod n) ℂ)ˣ) : Matrix (ZMod n) (ZMod n) ℂ) := by
          rw [hFval, mul_assoc]
      _ = (F : Matrix (ZMod n) (ZMod n) ℂ) * Matrix.diagonal (cycleEig n)
            * ((F⁻¹ : (Matrix (ZMod n) (ZMod n) ℂ)ˣ) : Matrix (ZMod n) (ZMod n) ℂ) := by
          rw [h, hFval]
  rw [hre, hL, spectrum.units_conjugate, spectrum_diagonal, range_cycleEig]

end Frontier.Spectral

