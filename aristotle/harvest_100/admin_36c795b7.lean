/-
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a plain comment at the very top of the file, since Lean does not
allow a module docstring to precede the `import` commands.)

We model the cycle graph `C n` on the vertex set `ZMod n` and its graph Laplacian as the circulant
matrix with `2` on the diagonal and `-1` on the two cyclic off-diagonals.  Conjugating by the
discrete Fourier matrix `F j k = exp (2 π i j k / n)` diagonalises it, which identifies the spectrum
as `{2 - 2 cos (2 π k / n) : k ∈ range n}`.
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

open Matrix

/-- The graph Laplacian of the cycle graph `C n`, indexed by `ZMod n`:
the circulant matrix with `2` on the diagonal and `-1` on the two cyclic off-diagonals. -/
def cycleLaplacian (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ := fun i j =>
  if i = j then 2 else if i - j = 1 ∨ j - i = 1 then -1 else 0

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

/-- The `k`-th eigenvalue of the cycle Laplacian. -/
noncomputable def cycleEigenvalue (n k : ℕ) : ℝ := 2 - 2 * Real.cos (2 * Real.pi * k / n)

section

variable (n : ℕ) [NeZero n]

theorem isPrimitiveRoot_zeta : IsPrimitiveRoot (zeta n) n :=
  Complex.isPrimitiveRoot_exp n (NeZero.ne n)

theorem zeta_pow_n : zeta n ^ n = 1 := (isPrimitiveRoot_zeta n).pow_eq_one

omit [NeZero n] in
theorem zeta_ne_zero : zeta n ≠ 0 := Complex.exp_ne_zero _

theorem zeta_pow_congr {a b : ℕ} (h : a % n = b % n) : zeta n ^ a = zeta n ^ b :=
  pow_eq_pow_of_modEq h (zeta_pow_n n)

/-- `2 - ζ^k - ζ^(-k) = 2 - 2 cos (2 π k / n)`. -/
theorem zeta_eigen (k : ℕ) :
    2 - zeta n ^ k - (zeta n ^ k)⁻¹ = ((cycleEigenvalue n k : ℝ) : ℂ) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [cycleEigenvalue, zeta]
  set t : ℝ := 2 * Real.pi * k / n with ht
  have h1 : (Complex.exp (2 * Real.pi * Complex.I / n)) ^ k = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    rw [ht]
    push_cast
    field_simp
  rw [h1, ← Complex.exp_neg]
  have h2 : -((t : ℂ) * Complex.I) = ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h2, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

/-- The discrete Fourier matrix `F j k = ζ ^ (j * k) = exp (2 π i j k / n)`. -/
noncomputable def fourier : Matrix (ZMod n) (ZMod n) ℂ := fun j k => zeta n ^ (j.val * k.val)

/-- The inverse discrete Fourier matrix. -/
noncomputable def fourierInv : Matrix (ZMod n) (ZMod n) ℂ := fun k m =>
  (n : ℂ)⁻¹ * zeta n ^ (k.val * (n - m.val))

theorem sum_zmod_eq_sum_range (f : ℕ → ℂ) :
    ∑ k : ZMod n, f k.val = ∑ i ∈ Finset.range n, f i := by
  refine Finset.sum_nbij' (i := ZMod.val) (j := (Nat.cast : ℕ → ZMod n)) ?_ ?_ ?_ ?_ ?_ <;>
    intro a ha <;>
      simp_all [ZMod.val_lt, ZMod.natCast_val, ZMod.val_natCast, Nat.mod_eq_of_lt]

theorem fourier_mul_fourierInv : fourier n * fourierInv n = 1 := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  ext j m
  rw [Matrix.mul_apply]
  have hterm : ∀ k : ZMod n,
      fourier n j k * fourierInv n k m
        = (n : ℂ)⁻¹ * (zeta n ^ (j.val + (n - m.val))) ^ k.val := by
    intro k
    have h : zeta n ^ (j.val * k.val) * zeta n ^ (k.val * (n - m.val))
        = (zeta n ^ (j.val + (n - m.val))) ^ k.val := by
      rw [← pow_add, ← pow_mul]; congr 1; ring
    simp only [fourier, fourierInv]
    rw [mul_left_comm, h]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum]
  rw [sum_zmod_eq_sum_range n (fun i => (zeta n ^ (j.val + (n - m.val))) ^ i)]
  by_cases hjm : j = m
  · subst hjm
    have hv : j.val + (n - j.val) = n := by have := ZMod.val_lt j; omega
    rw [hv, zeta_pow_n]
    simp [hn0]
  · have hjv : j.val ≠ m.val := fun h => hjm (by
      have := congrArg (Nat.cast : ℕ → ZMod n) h
      simpa [ZMod.natCast_val, ZMod.natCast_rightInverse] using this)
    have hjlt := ZMod.val_lt j
    have hmlt := ZMod.val_lt m
    have hne : zeta n ^ (j.val + (n - m.val)) ≠ 1 := by
      intro hcon
      have hdvd : n ∣ (j.val + (n - m.val)) :=
        (isPrimitiveRoot_zeta n).pow_eq_one_iff_dvd _ |>.mp hcon
      obtain ⟨c, hc⟩ := hdvd
      have hc0 : c ≠ 0 := by rintro rfl; omega
      have hc1 : c ≠ 1 := by rintro rfl; omega
      have h2c : n * 2 ≤ n * c := Nat.mul_le_mul_left n (by omega)
      omega
    have hpow : (zeta n ^ (j.val + (n - m.val))) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, zeta_pow_n, one_pow]
    rw [geom_sum_eq hne, hpow]
    simp [hjm]

theorem cycleLaplacian_apply_eq (hn : 3 ≤ n) (j m : ZMod n) :
    cycleLaplacian n j m =
      2 * (if m = j then 1 else 0) - (if m = j + 1 then 1 else 0)
        - (if m = j - 1 then 1 else 0) := by
  have h1 : (1 : ZMod n) ≠ 0 := by
    have : ((1 : ℕ) : ZMod n) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    simpa using this
  have h2 : (2 : ZMod n) ≠ 0 := by
    have : ((2 : ℕ) : ZMod n) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    simpa using this
  have hA : (j - m = 1) ↔ m = j - 1 := by
    constructor <;> intro h <;> linear_combination -h
  have hB : (m - j = 1) ↔ m = j + 1 := by
    constructor <;> intro h <;> linear_combination h
  have e3 : ¬ (j + 1 = j - 1) := fun h => h2 (by linear_combination h)
  have e4 : ¬ (j - 1 = j + 1) := fun h => h2 (by linear_combination -h)
  have e5 : ¬ (j = j - 1) := fun h => h1 (by linear_combination h)
  unfold cycleLaplacian
  simp only [hA, hB]
  by_cases hjm : m = j
  · subst hjm
    have e1 : ¬ (m = m + 1) := fun h => h1 (by linear_combination -h)
    have e2 : ¬ (m = m - 1) := fun h => h1 (by linear_combination h)
    simp [e1, e2]
  · have hjm' : ¬ (j = m) := fun h => hjm h.symm
    by_cases hp : m = j + 1
    · simp [hp, e3, h1]
    · by_cases hq : m = j - 1
      · simp [hq, e4, e5, h1]
      · simp [hjm, hjm', hp, hq]

theorem fourier_shift (hn : 3 ≤ n) (j k : ZMod n) :
    zeta n ^ ((j + 1).val * k.val) = zeta n ^ (j.val * k.val) * zeta n ^ k.val := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  rw [← pow_add]
  refine zeta_pow_congr n ?_
  rw [ZMod.val_add, ZMod.val_one]
  simp [Nat.add_mul]

theorem laplacian_mul_fourier (hn : 3 ≤ n) :
    cycleLaplacian n * fourier n =
      fourier n * Matrix.diagonal (fun k : ZMod n => ((cycleEigenvalue n k.val : ℝ) : ℂ)) := by
  ext j k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have hrow : ∀ m : ZMod n, cycleLaplacian n j m * fourier n m k
      = (if m = j then 2 * fourier n m k else 0) - (if m = j + 1 then fourier n m k else 0)
        - (if m = j - 1 then fourier n m k else 0) := by
    intro m
    rw [cycleLaplacian_apply_eq n hn]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun m _ => hrow m)]
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hplus : fourier n (j + 1) k = fourier n j k * zeta n ^ k.val := fourier_shift n hn j k
  have hminus : fourier n (j - 1) k = fourier n j k * (zeta n ^ k.val)⁻¹ := by
    have h := fourier_shift n hn (j - 1) k
    rw [sub_add_cancel] at h
    have hz : zeta n ^ k.val ≠ 0 := pow_ne_zero _ (zeta_ne_zero n)
    show zeta n ^ ((j - 1).val * k.val) = zeta n ^ (j.val * k.val) * (zeta n ^ k.val)⁻¹
    rw [h, mul_assoc, mul_inv_cancel₀ hz, mul_one]
  rw [hplus, hminus, ← zeta_eigen n k.val]
  ring

end

/-- **The Laplacian spectrum of the cycle graph `C n`.**  For `n ≥ 3`, the eigenvalues of the graph
Laplacian of the cycle `C n` (the circulant matrix with `2` on the diagonal and `-1` on the two
cyclic off-diagonals) are exactly the numbers `2 - 2 * cos (2 * π * k / n)` for `k ∈ range n`. -/
theorem cycle_laplacian_spectrum (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    spectrum ℂ (cycleLaplacian n) =
      (fun k : ℕ => ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ)) ''
        (Finset.range n : Set ℕ) := by
  have hFG := fourier_mul_fourierInv n
  have hGF : fourierInv n * fourier n = 1 := mul_eq_one_comm.mp hFG
  let u : (Matrix (ZMod n) (ZMod n) ℂ)ˣ := ⟨fourier n, fourierInv n, hFG, hGF⟩
  have hu : (u : Matrix (ZMod n) (ZMod n) ℂ) = fourier n := rfl
  have hu' : ((u⁻¹ : (Matrix (ZMod n) (ZMod n) ℂ)ˣ) : Matrix (ZMod n) (ZMod n) ℂ)
      = fourierInv n := rfl
  have hconj : cycleLaplacian n
      = (u : Matrix (ZMod n) (ZMod n) ℂ)
        * Matrix.diagonal (fun k : ZMod n => ((cycleEigenvalue n k.val : ℝ) : ℂ))
        * ((u⁻¹ : (Matrix (ZMod n) (ZMod n) ℂ)ˣ) : Matrix (ZMod n) (ZMod n) ℂ) := by
    rw [hu, hu', ← laplacian_mul_fourier n hn, Matrix.mul_assoc, hFG, Matrix.mul_one]
  rw [hconj, spectrum.units_conjugate, spectrum_diagonal]
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k.val, by simpa using ZMod.val_lt k, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    simp only [Finset.coe_range, Set.mem_Iio] at hk
    exact ⟨(k : ZMod n), by simp only [ZMod.val_natCast_of_lt hk, cycleEigenvalue]⟩

/-- Sanity check: the Laplacian spectrum of the triangle `C 3` is `{0, 3}`. -/
theorem cycle_laplacian_spectrum_three : spectrum ℂ (cycleLaplacian 3) = {0, 3} := by
  rw [cycle_laplacian_spectrum 3 le_rfl]
  have h0 : (2 * Real.pi * 0 / 3 : ℝ) = 0 := by ring
  have h1 : (2 * Real.pi * 1 / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
  have h2 : (2 * Real.pi * 2 / 3 : ℝ) = Real.pi + Real.pi / 3 := by ring
  have e1 : Real.cos (2 * Real.pi * 1 / 3) = -(1 / 2) := by
    rw [h1, Real.cos_pi_sub, Real.cos_pi_div_three]
  have e2 : Real.cos (2 * Real.pi * 2 / 3) = -(1 / 2) := by
    rw [h2, Real.cos_add, Real.cos_pi_div_three]
    simp
  have hr : (Finset.range 3 : Set ℕ) = {0, 1, 2} := by
    ext x; simp; omega
  rw [hr]
  simp only [Set.image_insert_eq, Set.image_singleton, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, h0, e1, e2, Real.cos_zero]
  norm_num

end Frontier.Spectral

