/-!
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
Statement: For n ≥ 3, the eigenvalues of the graph Laplacian L(C_n) of the cycle graph on n vertices are exactly { 2 - 2*Real.cos (2*Real.pi*k/n) : k ∈ Finset.range n }. Work self-contained over Mathlib: model C_n's Laplacian as the n×n circulant with diagonal 2 and -1 on the two cyclic off-diagonals, and exhibit the discrete-Fourier eigenvectors v_k(j) = Complex.exp (2*π*I*k*j/n).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Complex Matrix ZMod AddChar Finset

/-- The generating vector of the cycle Laplacian: `2` at `0`, `-1` at `±1`, `0` elsewhere. -/
noncomputable def cycleLapVec (n : ℕ) : ZMod n → ℂ :=
  fun d => if d = 0 then 2 else if d = 1 ∨ d = -1 then -1 else 0

/-- The graph Laplacian of the cycle graph `C n`, as the `n × n` circulant matrix with `2` on
the diagonal and `-1` on the two cyclic off-diagonals. -/
noncomputable def cycleLaplacian (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.circulant (cycleLapVec n)

/-- The discrete Fourier matrix, whose `k`-th column is the eigenvector
`v k j = exp (2 π I k j / n)`. -/
noncomputable def fourierMat (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.of fun i k => ZMod.stdAddChar (i * k)

/-- The inverse of the discrete Fourier matrix. -/
noncomputable def fourierMatInv (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.of fun k j => (n : ℂ)⁻¹ * ZMod.stdAddChar (-(k * j))

/-- The eigenvalue attached to the frequency `k`. -/
noncomputable def cycleEigen (n : ℕ) [NeZero n] (k : ZMod n) : ℂ :=
  2 - ZMod.stdAddChar k - ZMod.stdAddChar (-k)

section

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
lemma one_ne_zero_zmod (hn : 3 ≤ n) : (1 : ZMod n) ≠ 0 := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  exact one_ne_zero

omit [NeZero n] in
lemma neg_one_ne_zero_zmod (hn : 3 ≤ n) : (-1 : ZMod n) ≠ 0 := by
  simpa using one_ne_zero_zmod hn

omit [NeZero n] in
lemma one_ne_neg_one_zmod (hn : 3 ≤ n) : (1 : ZMod n) ≠ -1 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod n) = 0 := by push_cast; linear_combination h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

omit [NeZero n] in
/-- Rewriting of the generating vector as a combination of indicator functions. -/
lemma cycleLapVec_eq (hn : 3 ≤ n) (d : ZMod n) :
    cycleLapVec n d =
      2 * (if d = 0 then 1 else 0) - (if d = 1 then (1 : ℂ) else 0)
        - (if d = -1 then (1 : ℂ) else 0) := by
  have h1 : (1 : ZMod n) ≠ 0 := one_ne_zero_zmod hn
  have h2 : (-1 : ZMod n) ≠ 0 := neg_one_ne_zero_zmod hn
  have h3 : (1 : ZMod n) ≠ -1 := one_ne_neg_one_zmod hn
  unfold cycleLapVec
  by_cases hd0 : d = 0
  · subst hd0; simp [Ne.symm h1, Ne.symm h2]
  · by_cases hd1 : d = 1
    · subst hd1; simp [h1, h3]
    · by_cases hd2 : d = -1
      · subst hd2; simp [h2, Ne.symm h3]
      · simp [hd0, hd1, hd2]

/-- Evaluating a weighted sum against the generating vector. -/
lemma sum_cycleLapVec_mul (hn : 3 ≤ n) (f : ZMod n → ℂ) :
    ∑ d : ZMod n, cycleLapVec n d * f d = 2 * f 0 - f 1 - f (-1) := by
  simp only [cycleLapVec_eq hn, sub_mul, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp

/-- Orthogonality of the additive characters of `ZMod n`. -/
lemma sum_stdAddChar_mul (t : ZMod n) :
    ∑ i : ZMod n, ZMod.stdAddChar (t * i) = if t = 0 then (n : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar n h)

lemma fourier_mul_inv : fourierMat n * fourierMatInv n = 1 := by
  ext i j
  simp only [Matrix.mul_apply, fourierMat, fourierMatInv, Matrix.of_apply]
  have key : ∀ k : ZMod n, ZMod.stdAddChar (i * k) * ((n : ℂ)⁻¹ * ZMod.stdAddChar (-(k * j)))
      = (n : ℂ)⁻¹ * ZMod.stdAddChar ((i - j) * k) := by
    intro k
    rw [show (i - j) * k = i * k + -(k * j) by ring, AddChar.map_add_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.mul_sum, sum_stdAddChar_mul]
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  by_cases h : i = j
  · simp [h, Matrix.one_apply, hn]
  · simp [h, sub_eq_zero]

lemma inv_mul_fourier : fourierMatInv n * fourierMat n = 1 :=
  mul_eq_one_comm.mp fourier_mul_inv

/-- The Fourier matrix diagonalizes the cycle Laplacian. -/
lemma laplacian_mul_fourier (hn : 3 ≤ n) :
    cycleLaplacian n * fourierMat n = fourierMat n * Matrix.diagonal (cycleEigen n) := by
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have re : ∑ j : ZMod n, cycleLaplacian n i j * fourierMat n j k
      = ∑ d : ZMod n, cycleLapVec n d * ZMod.stdAddChar ((i - d) * k) := by
    refine (Fintype.sum_equiv (Equiv.subLeft i) _ _ ?_).symm
    intro d
    simp only [Equiv.subLeft_apply, cycleLaplacian, Matrix.circulant_apply, fourierMat,
      Matrix.of_apply]
    congr 2
    ring
  rw [re, sum_cycleLapVec_mul hn]
  simp only [fourierMat, Matrix.of_apply, cycleEigen]
  have e1 : ZMod.stdAddChar ((i - 1) * k) = ZMod.stdAddChar (i * k) * ZMod.stdAddChar (-k) := by
    rw [← AddChar.map_add_eq_mul]; congr 1; ring
  have e2 : ZMod.stdAddChar ((i - -1) * k) = ZMod.stdAddChar (i * k) * ZMod.stdAddChar k := by
    rw [← AddChar.map_add_eq_mul]; congr 1; ring
  rw [e1, e2, sub_zero]
  ring

/-- The eigenvalues are `2 - 2 cos (2 π k / n)`. -/
lemma cycleEigen_eq (k : ZMod n) :
    cycleEigen n k = ((2 - 2 * Real.cos (2 * Real.pi * k.val / n) : ℝ) : ℂ) := by
  have hk : ((k.val : ℤ) : ZMod n) = k := by push_cast [ZMod.natCast_val, ZMod.cast_id]; ring
  have h1 : ZMod.stdAddChar k = Complex.exp (2 * Real.pi * I * (k.val : ℂ) / n) := by
    conv_lhs => rw [← hk]
    rw [ZMod.stdAddChar_coe]; push_cast; ring_nf
  have h2 : ZMod.stdAddChar (-k) = Complex.exp (-(2 * Real.pi * I * (k.val : ℂ) / n)) := by
    conv_lhs => rw [← hk, ← Int.cast_neg, ZMod.stdAddChar_coe]
    push_cast; ring_nf
  rw [cycleEigen, h1, h2]
  push_cast
  have h3 := Complex.two_cos ((2 * (Real.pi : ℂ) * (k.val : ℂ) / n))
  rw [neg_mul] at h3
  rw [show (2 * (Real.pi : ℂ) * I * (k.val : ℂ) / n)
      = ((2 * (Real.pi : ℂ) * (k.val : ℂ) / n) * I) by ring]
  linear_combination h3

/-- The cycle Laplacian is conjugate, via the Fourier matrix, to the diagonal matrix of
eigenvalues. -/
lemma laplacian_eq_conj (hn : 3 ≤ n) :
    cycleLaplacian n
      = fourierMat n * Matrix.diagonal (cycleEigen n) * fourierMatInv n := by
  calc cycleLaplacian n = cycleLaplacian n * (fourierMat n * fourierMatInv n) := by
        rw [fourier_mul_inv, Matrix.mul_one]
    _ = (cycleLaplacian n * fourierMat n) * fourierMatInv n := by rw [Matrix.mul_assoc]
    _ = fourierMat n * Matrix.diagonal (cycleEigen n) * fourierMatInv n := by
        rw [laplacian_mul_fourier hn]

lemma spectrum_cycleLaplacian (hn : 3 ≤ n) :
    spectrum ℂ (cycleLaplacian n) = Set.range (cycleEigen n) := by
  set u : (Matrix (ZMod n) (ZMod n) ℂ)ˣ :=
    ⟨fourierMat n, fourierMatInv n, fourier_mul_inv, inv_mul_fourier⟩ with hu
  have hconj : cycleLaplacian n
      = (u : Matrix (ZMod n) (ZMod n) ℂ) * Matrix.diagonal (cycleEigen n)
        * ((u⁻¹ : (Matrix (ZMod n) (ZMod n) ℂ)ˣ) : Matrix (ZMod n) (ZMod n) ℂ) :=
    laplacian_eq_conj hn
  rw [hconj, spectrum.units_conjugate, _root_.spectrum_diagonal]

end

/-- **Spectrum of the cycle Laplacian.** For `n ≥ 3`, the eigenvalues of the graph Laplacian
of the cycle graph `C n` (modelled as the `n × n` circulant matrix with diagonal `2` and `-1`
on the two cyclic off-diagonals, diagonalized by the discrete Fourier eigenvectors
`v k j = exp (2 π I k j / n)`) are exactly the numbers `2 - 2 cos (2 π k / n)` for
`k = 0, …, n - 1`. -/
theorem cycle_laplacian_spectrum (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    spectrum ℂ (cycleLaplacian n) =
      (fun k : ℕ => ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ)) ''
        (Finset.range n : Set ℕ) := by
  rw [spectrum_cycleLaplacian hn]
  ext z
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k.val, by simpa using ZMod.val_lt k, (cycleEigen_eq k).symm⟩
  · rintro ⟨k, hk, rfl⟩
    simp only [Finset.coe_range, Set.mem_Iio] at hk
    refine ⟨(k : ZMod n), ?_⟩
    rw [cycleEigen_eq, ZMod.val_natCast_of_lt hk]

end Frontier.Spectral

