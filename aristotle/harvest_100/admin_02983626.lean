import Mathlib
/-!
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
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

open Matrix Finset

/-- The graph Laplacian of the cycle `C n`, as the `n × n` circulant matrix (indexed by
`ZMod n`) with diagonal entries `2` and `-1` on the two cyclic off-diagonals. -/
def cycleLaplacian (n : ℕ) : Matrix (ZMod n) (ZMod n) ℂ :=
  fun i j => if i = j then 2 else if i = j + 1 ∨ i = j - 1 then -1 else 0

variable {n : ℕ} [NeZero n]

/-- The matrix of discrete Fourier eigenvectors: `W i j = exp (2 π I i j / n)`, whose `k`-th
column is the vector `v k (j) = exp (2 π I k j / n)`. -/
noncomputable def fourierMatrix (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  fun i j => ZMod.stdAddChar (i * j)

/-- The inverse of the Fourier matrix (the conjugate matrix, scaled by `1/n`). -/
noncomputable def fourierMatrixInv (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  fun i j => (n : ℂ)⁻¹ * ZMod.stdAddChar (-(i * j))

/-- The eigenvalue attached to the Fourier mode `k`. -/
noncomputable def cycleEigenvalue (n : ℕ) [NeZero n] (k : ZMod n) : ℂ :=
  2 - ZMod.stdAddChar k - ZMod.stdAddChar (-k)

/-- Orthogonality of the standard additive character on `ZMod n`. -/
lemma sum_stdAddChar_mul (t : ZMod n) :
    ∑ i : ZMod n, ZMod.stdAddChar (t * i) = if t = 0 then (n : ℂ) else 0 := by
  split_ifs with h
  · simp [h, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar n h)

omit [NeZero n] in
lemma one_ne_zero_zmod (hn : 3 ≤ n) : (1 : ZMod n) ≠ 0 := by
  intro h
  have h2 : ((1 : ℕ) : ZMod n) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd one_pos h2
  omega

omit [NeZero n] in
lemma two_ne_zero_zmod (hn : 3 ≤ n) : (2 : ZMod n) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod n) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

omit [NeZero n] in
/-- The three-term description of the rows of the cycle Laplacian: the neighbours `i + 1`,
`i - 1` of `i` are distinct from each other and from `i` as soon as `3 ≤ n`. -/
lemma cycleLaplacian_apply (hn : 3 ≤ n) (i j : ZMod n) :
    cycleLaplacian n i j =
      2 * (if j = i then 1 else 0) - (if j = i + 1 then 1 else 0)
        - (if j = i - 1 then 1 else 0) := by
  have h1 := one_ne_zero_zmod hn
  have h2 := two_ne_zero_zmod hn
  have hA : ∀ x : ZMod n, x ≠ x + 1 := fun x h => h1 (by linear_combination -h)
  have hB : ∀ x : ZMod n, x ≠ x - 1 := fun x h => h1 (by linear_combination h)
  have hC : ∀ x : ZMod n, x + 1 ≠ x - 1 := fun x h => h2 (by linear_combination h)
  have c2 : (i = j + 1) ↔ (j = i - 1) := by
    constructor <;> intro h <;> rw [h] <;> ring
  have c3 : (i = j - 1) ↔ (j = i + 1) := by
    constructor <;> intro h <;> rw [h] <;> ring
  simp only [cycleLaplacian, eq_comm (a := i) (b := j), c2, c3]
  by_cases hji : j = i
  · subst hji
    simp [hA j, hB j]
  · by_cases hj1 : j = i + 1
    · subst hj1
      simp [hji, hC i]
    · by_cases hj2 : j = i - 1
      · subst hj2
        simp [hji, hj1]
      · simp [hji, hj1, hj2]

/-- Multiplying a row of the Laplacian against an arbitrary vector. -/
lemma cycleLaplacian_row_sum (hn : 3 ≤ n) (i : ZMod n) (f : ZMod n → ℂ) :
    ∑ j : ZMod n, cycleLaplacian n i j * f j = 2 * f i - f (i + 1) - f (i - 1) := by
  simp [cycleLaplacian_apply hn, sub_mul, ite_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq']

/-- The Fourier vectors diagonalise the cycle Laplacian. -/
lemma cycleLaplacian_mul_fourierMatrix (hn : 3 ≤ n) :
    cycleLaplacian n * fourierMatrix n = fourierMatrix n * diagonal (cycleEigenvalue n) := by
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_diagonal,
    cycleLaplacian_row_sum hn i (fun j => fourierMatrix n j k)]
  simp only [fourierMatrix, cycleEigenvalue]
  rw [show ((i + 1) * k) = i * k + k by ring, show ((i - 1) * k) = i * k + -k by ring,
    AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  ring

lemma fourierMatrix_mul_inv : fourierMatrix n * fourierMatrixInv n = 1 := by
  ext i l
  rw [Matrix.mul_apply]
  simp only [fourierMatrix, fourierMatrixInv, Matrix.one_apply]
  have key : ∀ j : ZMod n, ZMod.stdAddChar (i * j) * ((n : ℂ)⁻¹ * ZMod.stdAddChar (-(j * l)))
      = (n : ℂ)⁻¹ * ZMod.stdAddChar ((i - l) * j) := by
    intro j
    rw [show ((i - l) * j) = i * j + -(j * l) by ring, AddChar.map_add_eq_mul]
    ring
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  simp only [key, ← Finset.mul_sum, sum_stdAddChar_mul, sub_eq_zero]
  split_ifs <;> simp [inv_mul_cancel₀ hn0]

lemma fourierMatrixInv_mul : fourierMatrixInv n * fourierMatrix n = 1 := by
  ext i l
  rw [Matrix.mul_apply]
  simp only [fourierMatrix, fourierMatrixInv, Matrix.one_apply]
  have key : ∀ j : ZMod n, ((n : ℂ)⁻¹ * ZMod.stdAddChar (-(i * j))) * ZMod.stdAddChar (j * l)
      = (n : ℂ)⁻¹ * ZMod.stdAddChar ((l - i) * j) := by
    intro j
    rw [show ((l - i) * j) = -(i * j) + j * l by ring, AddChar.map_add_eq_mul]
    ring
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  simp only [key, ← Finset.mul_sum, sum_stdAddChar_mul, sub_eq_zero,
    eq_comm (a := l) (b := i)]
  split_ifs <;> simp [inv_mul_cancel₀ hn0]

/-- The Fourier matrix as a unit of the matrix algebra. -/
noncomputable def fourierUnit (n : ℕ) [NeZero n] : (Matrix (ZMod n) (ZMod n) ℂ)ˣ where
  val := fourierMatrix n
  inv := fourierMatrixInv n
  val_inv := fourierMatrix_mul_inv
  inv_val := fourierMatrixInv_mul

/-- The `k`-th eigenvalue is the real number `2 - 2 cos (2 π k / n)`. -/
lemma cycleEigenvalue_eq (k : ZMod n) :
    cycleEigenvalue n k = ((2 - 2 * Real.cos (2 * Real.pi * k.val / n) : ℝ) : ℂ) := by
  have hk : ((k.val : ℤ) : ZMod n) = k := by push_cast [ZMod.natCast_val, ZMod.cast_id]; ring
  have h1 : ZMod.stdAddChar k
      = Complex.exp ((2 * (Real.pi : ℂ) * (k.val : ℕ) / n) * Complex.I) := by
    conv_lhs => rw [← hk]
    rw [ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  have h2 : ZMod.stdAddChar (-k)
      = Complex.exp (-(2 * (Real.pi : ℂ) * (k.val : ℕ) / n) * Complex.I) := by
    conv_lhs => rw [show (-k) = (((-(k.val : ℤ)) : ℤ) : ZMod n) by rw [Int.cast_neg, hk]]
    rw [ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  have hc := Complex.two_cos ((2 * (Real.pi : ℂ) * (k.val : ℕ) / n))
  rw [cycleEigenvalue, h1, h2]
  push_cast [Complex.ofReal_cos]
  linear_combination hc

/-- **Spectrum of the cycle Laplacian.** For `n ≥ 3`, the eigenvalues of the graph Laplacian
of the cycle `C n` are exactly the numbers `2 - 2 cos (2 π k / n)` for `k ∈ Finset.range n`. -/
theorem cycle_laplacian_spectrum (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    spectrum ℂ (cycleLaplacian n) =
      (fun k : ℕ => ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ)) ''
        (Finset.range n : Finset ℕ) := by
  have hconj : cycleLaplacian n
      = (fourierUnit n : Matrix (ZMod n) (ZMod n) ℂ) * diagonal (cycleEigenvalue n)
          * ((fourierUnit n)⁻¹ : (Matrix (ZMod n) (ZMod n) ℂ)ˣ) := by
    have : cycleLaplacian n * fourierMatrix n * fourierMatrixInv n
        = fourierMatrix n * diagonal (cycleEigenvalue n) * fourierMatrixInv n := by
      rw [cycleLaplacian_mul_fourierMatrix hn]
    rw [mul_assoc, fourierMatrix_mul_inv, mul_one] at this
    exact this
  rw [hconj, spectrum.units_conjugate, spectrum_diagonal]
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k.val, by simpa using ZMod.val_lt k, (cycleEigenvalue_eq k).symm⟩
  · rintro ⟨m, hm, rfl⟩
    refine ⟨(m : ZMod n), ?_⟩
    rw [cycleEigenvalue_eq, ZMod.val_natCast_of_lt (Finset.mem_range.mp hm)]

/-- The discrete Fourier vector `v k (j) = exp (2 π I k j / n)` is an eigenvector of the cycle
Laplacian, with eigenvalue `2 - 2 cos (2 π k / n)`. -/
lemma cycleLaplacian_mulVec_fourierVec (hn : 3 ≤ n) (k : ZMod n) :
    cycleLaplacian n *ᵥ (fun j => ZMod.stdAddChar (j * k))
      = ((2 - 2 * Real.cos (2 * Real.pi * k.val / n) : ℝ) : ℂ) •
          (fun j => ZMod.stdAddChar (j * k)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [cycleLaplacian_row_sum hn i (fun j => ZMod.stdAddChar (j * k)), ← cycleEigenvalue_eq,
    cycleEigenvalue, show ((i + 1) * k) = i * k + k by ring,
    show ((i - 1) * k) = i * k + -k by ring, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  ring

/-- Membership in the spectrum of a matrix is having an eigenvector. -/
lemma mem_spectrum_iff_exists_eigenvector (A : Matrix (ZMod n) (ZMod n) ℂ) (mu : ℂ) :
    (∃ v : ZMod n → ℂ, v ≠ 0 ∧ A *ᵥ v = mu • v) ↔ mu ∈ spectrum ℂ A := by
  rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum]
  constructor
  · rintro ⟨v, hv, h⟩
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (by simpa [Matrix.toLin'_apply] using h), hv⟩
  · intro h
    obtain ⟨v, hv1, hv2⟩ := h.exists_hasEigenvector
    exact ⟨v, hv2, by simpa [Matrix.toLin'_apply] using Module.End.mem_eigenspace_iff.mp hv1⟩

/-- Eigenvector form of the main theorem: for `n ≥ 3`, a complex number `mu` admits a nonzero
eigenvector for the cycle Laplacian iff `mu = 2 - 2 cos (2 π k / n)` for some `k < n`. -/
theorem cycle_laplacian_eigenvalue_iff (n : ℕ) [NeZero n] (hn : 3 ≤ n) (mu : ℂ) :
    (∃ v : ZMod n → ℂ, v ≠ 0 ∧ cycleLaplacian n *ᵥ v = mu • v)
      ↔ ∃ k < n, mu = ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ) := by
  rw [mem_spectrum_iff_exists_eigenvector, cycle_laplacian_spectrum n hn]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, Finset.mem_range.mp hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, Finset.mem_coe.mpr (Finset.mem_range.mpr hk), rfl⟩

end Frontier.Spectral

