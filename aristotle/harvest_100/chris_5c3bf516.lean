/-
# Cycle Laplacian Spectrum
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cycle Laplacian Spectrum
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier.Spectral

open Complex Finset Matrix

/-! ## Definitions -/

/-- The `n`-th root of unity `exp (2πI/n)`. -/
noncomputable def zetaN (n : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))

/-- The first column of the cycle Laplacian: `2` on the diagonal, `-1` on the two cyclic
off-diagonals. -/
noncomputable def cycleVec (n : ℕ) : Fin n → ℂ :=
  fun i => if (i : ℕ) = 0 then 2 else if (i : ℕ) = 1 ∨ (i : ℕ) = n - 1 then -1 else 0

/-- The graph Laplacian of the cycle graph `C n`, as the circulant matrix with diagonal `2`
and `-1` on the two cyclic off-diagonals. -/
noncomputable def cycleLaplacian (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.circulant (cycleVec n)

/-- The `k`-th eigenvalue `2 - 2 cos (2πk/n)`. -/
noncomputable def cycleEig (n : ℕ) : Fin n → ℂ :=
  fun k => ((2 - 2 * Real.cos (2 * Real.pi * (k : ℕ) / n) : ℝ) : ℂ)

/-- The discrete Fourier matrix, whose `k`-th column is the eigenvector
`v k j = exp (2πI k j / n)`. -/
noncomputable def dftMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => zetaN n ^ ((j : ℕ) * (k : ℕ))

/-- The inverse of the discrete Fourier matrix. -/
noncomputable def dftInvMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => (n : ℂ)⁻¹ * (zetaN n ^ ((j : ℕ) * (k : ℕ)))⁻¹

/-- Sanity check: for `n = 3` the definition is the usual Laplacian of the triangle. -/
theorem cycleLaplacian_three :
    cycleLaplacian 3 = !![2, -1, -1; -1, 2, -1; -1, -1, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycleLaplacian, cycleVec, Matrix.circulant_apply, Fin.sub_def, Fin.ext_iff]
  all_goals decide

/-! ## Basic facts about `zetaN` -/

theorem zetaN_ne_zero (n : ℕ) : zetaN n ≠ 0 := Complex.exp_ne_zero _

theorem isPrimitiveRoot_zetaN {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (zetaN n) n := by
  have := Complex.isPrimitiveRoot_exp n hn
  simpa [zetaN] using this

theorem zetaN_pow_n {n : ℕ} (hn : n ≠ 0) : zetaN n ^ n = 1 :=
  (isPrimitiveRoot_zetaN hn).pow_eq_one

theorem zetaN_pow_mod {n : ℕ} (hn : n ≠ 0) (a : ℕ) : zetaN n ^ (a % n) = zetaN n ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a n]
  rw [pow_add, pow_mul, zetaN_pow_n hn, one_pow, one_mul]

theorem zetaN_pow_congr {n : ℕ} (hn : n ≠ 0) {a b : ℕ} (h : a % n = b % n) :
    zetaN n ^ a = zetaN n ^ b := by
  rw [← zetaN_pow_mod hn a, ← zetaN_pow_mod hn b, h]

/-- `ζ^k + (ζ^k)⁻¹ = 2 cos (2πk/n)`. -/
theorem zetaN_pow_add_inv {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    zetaN n ^ k + (zetaN n ^ k)⁻¹ = ((2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hz : zetaN n ^ k = Complex.exp (((2 * Real.pi * k / n : ℝ) : ℂ) * Complex.I) := by
    rw [zetaN, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have hz' : (zetaN n ^ k)⁻¹ = Complex.exp (-((2 * Real.pi * k / n : ℝ) : ℂ) * Complex.I) := by
    rw [hz, ← Complex.exp_neg]
    congr 1
    ring
  rw [hz', hz, ← Complex.two_cos]
  push_cast
  ring

/-! ## Invertibility of the DFT matrix -/

theorem dftInv_mul_dft {n : ℕ} (hn : n ≠ 0) :
    dftInvMatrix n * dftMatrix n = 1 := by
  have hz0 : zetaN n ≠ 0 := zetaN_ne_zero n
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  ext j l
  rw [Matrix.mul_apply]
  have key : ∀ k : Fin n,
      dftInvMatrix n j k * dftMatrix n k l
        = (n : ℂ)⁻¹ * ((zetaN n ^ (l : ℕ)) * (zetaN n ^ (j : ℕ))⁻¹) ^ (k : ℕ) := by
    intro k
    have h1 : ((zetaN n ^ (l : ℕ)) * (zetaN n ^ (j : ℕ))⁻¹) ^ (k : ℕ)
        = zetaN n ^ ((k : ℕ) * (l : ℕ)) * (zetaN n ^ ((j : ℕ) * (k : ℕ)))⁻¹ := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm (l : ℕ) (k : ℕ),
        mul_comm (j : ℕ) (k : ℕ)]
    simp only [dftInvMatrix, dftMatrix, h1]
    ring
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.mul_sum]
  have hsum : ∑ k : Fin n, ((zetaN n ^ (l : ℕ)) * (zetaN n ^ (j : ℕ))⁻¹) ^ (k : ℕ)
      = ∑ k ∈ Finset.range n, ((zetaN n ^ (l : ℕ)) * (zetaN n ^ (j : ℕ))⁻¹) ^ k :=
    Fin.sum_univ_eq_sum_range
      (fun k => ((zetaN n ^ (l : ℕ)) * (zetaN n ^ (j : ℕ))⁻¹) ^ k) n
  rw [hsum]
  by_cases hjl : j = l
  · have hx1 : (zetaN n ^ (l : ℕ)) * (zetaN n ^ (j : ℕ))⁻¹ = 1 := by
      rw [hjl]
      exact mul_inv_cancel₀ (pow_ne_zero _ hz0)
    rw [hx1, hjl, Matrix.one_apply_eq]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ hnC
  · have hjne : zetaN n ^ (j : ℕ) ≠ 0 := pow_ne_zero _ hz0
    have hxne : (zetaN n ^ (l : ℕ)) * (zetaN n ^ (j : ℕ))⁻¹ ≠ 1 := by
      intro hx1
      rw [mul_inv_eq_one₀ hjne] at hx1
      exact hjl (Fin.ext ((isPrimitiveRoot_zetaN hn).pow_inj l.isLt j.isLt hx1)).symm
    have hxn : ((zetaN n ^ (l : ℕ)) * (zetaN n ^ (j : ℕ))⁻¹) ^ n = 1 := by
      have h1 : (zetaN n ^ (l : ℕ)) ^ n = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, zetaN_pow_n hn, one_pow]
      have h2 : (zetaN n ^ (j : ℕ)) ^ n = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, zetaN_pow_n hn, one_pow]
      rw [mul_pow, inv_pow, h1, h2, inv_one, mul_one]
    rw [geom_sum_eq hxne, hxn, Matrix.one_apply_ne hjl]
    simp

/-- The DFT matrix is invertible. -/
noncomputable def dftInvertible {n : ℕ} (hn : n ≠ 0) : Invertible (dftMatrix n) :=
  invertibleOfLeftInverse _ _ (dftInv_mul_dft hn)

/-! ## The Fourier vectors are eigenvectors -/

/-- The weighted sum of the circulant vector against the characters, giving the eigenvalue. -/
theorem cycleVec_sum {n : ℕ} (hn : 3 ≤ n) (k : Fin n) :
    ∑ m : Fin n, cycleVec n m * zetaN n ^ ((n - (m : ℕ)) * (k : ℕ)) = cycleEig n k := by
  have hn0 : n ≠ 0 := by omega
  have hz0 : zetaN n ≠ 0 := zetaN_ne_zero n
  have hpow : ∀ a : ℕ, zetaN n ^ (n * a) = 1 := by
    intro a
    rw [pow_mul, zetaN_pow_n hn0, one_pow]
  obtain ⟨a0, ha0⟩ : ∃ a : Fin n, (a : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨a1, ha1⟩ : ∃ a : Fin n, (a : ℕ) = 1 := ⟨⟨1, by omega⟩, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ a : Fin n, (a : ℕ) = n - 1 := ⟨⟨n - 1, by omega⟩, rfl⟩
  have hsub : ({a0, a1, a2} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
  have hzero : ∀ m ∈ (Finset.univ : Finset (Fin n)), m ∉ ({a0, a1, a2} : Finset (Fin n)) →
      cycleVec n m * zetaN n ^ ((n - (m : ℕ)) * (k : ℕ)) = 0 := by
    intro m _ hm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or, Fin.ext_iff, ha0, ha1, ha2] at hm
    obtain ⟨h0, h1, h2⟩ := hm
    simp [cycleVec, h0, h1, h2]
  rw [← Finset.sum_subset hsub hzero,
    Finset.sum_insert (by simp [Finset.mem_insert, Fin.ext_iff, ha0, ha1, ha2]; omega),
    Finset.sum_insert (by simp [Finset.mem_singleton, Fin.ext_iff, ha1, ha2]; omega),
    Finset.sum_singleton]
  have e0 : cycleVec n a0 * zetaN n ^ ((n - (a0 : ℕ)) * (k : ℕ)) = 2 := by
    have hv : cycleVec n a0 = 2 := by simp [cycleVec, ha0]
    rw [hv, ha0, Nat.sub_zero, hpow, mul_one]
  have e1 : cycleVec n a1 * zetaN n ^ ((n - (a1 : ℕ)) * (k : ℕ)) = -(zetaN n ^ (k : ℕ))⁻¹ := by
    have hv : cycleVec n a1 = -1 := by simp [cycleVec, ha1]
    have hmul : (zetaN n ^ ((n - 1) * (k : ℕ))) * (zetaN n ^ (k : ℕ)) = 1 := by
      rw [← pow_add]
      have hexp : (n - 1) * (k : ℕ) + (k : ℕ) = n * (k : ℕ) := by
        have : 1 ≤ n := by omega
        cases' Nat.exists_eq_add_of_le this with c hc
        subst hc
        simp [Nat.add_mul]
        ring
      rw [hexp, hpow]
    have hinv : zetaN n ^ ((n - 1) * (k : ℕ)) = (zetaN n ^ (k : ℕ))⁻¹ :=
      eq_inv_of_mul_eq_one_left hmul
    rw [hv, ha1, hinv]
    ring
  have e2 : cycleVec n a2 * zetaN n ^ ((n - (a2 : ℕ)) * (k : ℕ)) = -(zetaN n ^ (k : ℕ)) := by
    have hv : cycleVec n a2 = -1 := by
      have hne : n - 1 ≠ 0 := by omega
      simp [cycleVec, hne, ha2]
    have hn1 : n - (a2 : ℕ) = 1 := by rw [ha2]; omega
    rw [hv, hn1, one_mul]
    ring
  rw [e0, e1, e2, cycleEig]
  have hcos := zetaN_pow_add_inv hn0 (k : ℕ)
  push_cast at hcos ⊢
  linear_combination -hcos

theorem laplacian_mul_dft {n : ℕ} (hn : 3 ≤ n) :
    cycleLaplacian n * dftMatrix n = dftMatrix n * Matrix.diagonal (cycleEig n) := by
  have hn0 : n ≠ 0 := by omega
  haveI : NeZero n := ⟨hn0⟩
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hrhs : ∑ j : Fin n, dftMatrix n i j * Matrix.diagonal (cycleEig n) j k
      = dftMatrix n i k * cycleEig n k := by
    simp [Matrix.diagonal_apply, eq_comm]
  rw [hrhs]
  have hlhs : ∀ j : Fin n, cycleLaplacian n i j * dftMatrix n j k
      = cycleVec n (i - j) * zetaN n ^ ((j : ℕ) * (k : ℕ)) := by
    intro j
    simp [cycleLaplacian, Matrix.circulant_apply, dftMatrix]
  rw [Finset.sum_congr rfl (fun j _ => hlhs j)]
  have hre : ∑ j : Fin n, cycleVec n (i - j) * zetaN n ^ ((j : ℕ) * (k : ℕ))
      = ∑ m : Fin n, cycleVec n m * zetaN n ^ (((i - m : Fin n) : ℕ) * (k : ℕ)) := by
    refine (Equiv.sum_comp (Equiv.subLeft i)
      (fun j : Fin n => cycleVec n (i - j) * zetaN n ^ ((j : ℕ) * (k : ℕ)))).symm.trans ?_
    refine Finset.sum_congr rfl ?_
    intro m _
    simp only [Equiv.subLeft_apply]
    rw [sub_sub_cancel]
  rw [hre]
  have hstep : ∀ m : Fin n, cycleVec n m * zetaN n ^ (((i - m : Fin n) : ℕ) * (k : ℕ))
      = zetaN n ^ ((i : ℕ) * (k : ℕ)) * (cycleVec n m * zetaN n ^ ((n - (m : ℕ)) * (k : ℕ))) := by
    intro m
    have hval : ((i - m : Fin n) : ℕ) = (n - (m : ℕ) + (i : ℕ)) % n := Fin.val_sub i m
    have hcong : (((i - m : Fin n) : ℕ) * (k : ℕ)) % n
        = ((n - (m : ℕ) + (i : ℕ)) * (k : ℕ)) % n := by
      rw [hval, Nat.mul_mod, Nat.mod_mod_of_dvd, ← Nat.mul_mod]
      exact dvd_rfl
    rw [zetaN_pow_congr hn0 hcong, add_mul, pow_add]
    ring
  rw [Finset.sum_congr rfl (fun m _ => hstep m), ← Finset.mul_sum, cycleVec_sum hn]
  simp [dftMatrix]

/-- The entries of the DFT matrix are the discrete Fourier characters. -/
theorem dftMatrix_apply_eq_exp {n : ℕ} (hn : n ≠ 0) (j k : Fin n) :
    dftMatrix n j k
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℕ) * (j : ℕ) / (n : ℂ)) := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [dftMatrix, zetaN, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- The discrete Fourier vectors `v k j = exp (2πI k j / n)` are eigenvectors of the cycle
Laplacian, with eigenvalue `2 - 2 cos (2πk/n)`. -/
theorem cycleLaplacian_mulVec_fourier {n : ℕ} (hn : 3 ≤ n) (k : Fin n) :
    (cycleLaplacian n).mulVec
        (fun j : Fin n => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℕ) * (j : ℕ) / (n : ℂ)))
      = ((2 - 2 * Real.cos (2 * Real.pi * (k : ℕ) / n) : ℝ) : ℂ) •
        (fun j : Fin n =>
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℕ) * (j : ℕ) / (n : ℂ))) := by
  have hn0 : n ≠ 0 := by omega
  funext i
  have h := congrFun (congrFun (laplacian_mul_dft hn) i) k
  have hrhs : ∑ j : Fin n, dftMatrix n i j * Matrix.diagonal (cycleEig n) j k
      = dftMatrix n i k * cycleEig n k := by
    simp [Matrix.diagonal_apply, eq_comm]
  rw [Matrix.mul_apply, Matrix.mul_apply, hrhs] at h
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
    ← dftMatrix_apply_eq_exp hn0]
  rw [h, cycleEig]
  ring

/-! ## The main theorem -/

/-- **Cycle Laplacian spectrum.** For `n ≥ 3`, the spectrum of the Laplacian of the cycle
graph `C n` (modelled as the circulant matrix with diagonal `2` and `-1` on the two cyclic
off-diagonals) is exactly `{2 - 2 cos (2πk/n) : k ∈ range n}`. -/
theorem cycle_laplacian_spectrum (n : ℕ) (hn : 3 ≤ n) :
    spectrum ℂ (cycleLaplacian n) =
      (fun k : ℕ => ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ)) ''
        (Finset.range n : Set ℕ) := by
  have hn0 : n ≠ 0 := by omega
  haveI : Invertible (dftMatrix n) := dftInvertible hn0
  set u : (Matrix (Fin n) (Fin n) ℂ)ˣ := unitOfInvertible (dftMatrix n) with hu
  have hU : (u : Matrix (Fin n) (Fin n) ℂ) = dftMatrix n := rfl
  have hconj : cycleLaplacian n
      = (u : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal (cycleEig n)
          * ((u⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
    calc cycleLaplacian n
        = cycleLaplacian n * (u : Matrix (Fin n) (Fin n) ℂ)
            * ((u⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = (u : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal (cycleEig n)
            * ((u⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
          rw [hU, laplacian_mul_dft hn]
  rw [hconj, spectrum.units_conjugate, spectrum_diagonal]
  ext μ
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨(k : ℕ), by simp, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    simp only [Finset.coe_range, Set.mem_Iio] at hk
    exact ⟨⟨k, hk⟩, rfl⟩

end Frontier.Spectral

