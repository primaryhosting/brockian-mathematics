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

open Matrix

/-- The graph Laplacian of the cycle graph `C n`: the `n × n` circulant matrix with `2` on the
diagonal and `-1` on the two cyclic off-diagonals. -/
def cycleLaplacian (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j =>
    if i = j then 2
    else if (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val then -1 else 0

/-- The primitive `n`-th root of unity `exp (2 π I / n)`. -/
noncomputable def cycleRoot (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

/-- The `k`-th eigenvalue of the cycle Laplacian, in the form `2 - ω ^ k - ω ^ (-k)`. -/
noncomputable def cycleEig (n k : ℕ) : ℂ := 2 - cycleRoot n ^ k - (cycleRoot n ^ k)⁻¹

/-- The discrete Fourier matrix; its `k`-th column is the eigenvector
`v_k (j) = exp (2 π I k j / n)`. -/
noncomputable def fourierMat (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => cycleRoot n ^ (i.val * j.val)

/-- The inverse of the discrete Fourier matrix. -/
noncomputable def fourierMatInv (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => (n : ℂ)⁻¹ * (cycleRoot n ^ (i.val * j.val))⁻¹

lemma cycleRoot_ne_zero (n : ℕ) : cycleRoot n ≠ 0 := Complex.exp_ne_zero _

lemma cycleRoot_isPrimitiveRoot {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (cycleRoot n) n :=
  Complex.isPrimitiveRoot_exp n hn

lemma cycleRoot_pow_n {n : ℕ} (hn : n ≠ 0) : cycleRoot n ^ n = 1 :=
  (cycleRoot_isPrimitiveRoot hn).pow_eq_one

lemma pow_mod_of_pow_eq_one {n : ℕ} {z : ℂ} (hz : z ^ n = 1) (a : ℕ) :
    z ^ (a % n) = z ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a n, pow_add, pow_mul, hz, one_pow, one_mul]

/-- Orthogonality of characters: the powers of an `n`-th root of unity sum to `n` or to `0`. -/
lemma sum_pow_eq {n : ℕ} {z : ℂ} (hz : z ^ n = 1) :
    ∑ p : Fin n, z ^ (p : ℕ) = if z = 1 then (n : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => z ^ i) n]
  by_cases h : z = 1
  · simp [h]
  · rw [if_neg h, geom_sum_eq h, hz, sub_self, zero_div]

lemma fourier_mul_inv {n : ℕ} (hn : n ≠ 0) : fourierMat n * fourierMatInv n = 1 := by
  have hw := cycleRoot_pow_n hn
  have hpow : ∀ m : ℕ, (cycleRoot n ^ m) ^ n = 1 := by
    intro m; rw [← pow_mul, mul_comm, pow_mul, hw, one_pow]
  have hne : ∀ m : ℕ, cycleRoot n ^ m ≠ 0 := fun m => pow_ne_zero _ (cycleRoot_ne_zero n)
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  set z : ℂ := cycleRoot n ^ i.val * (cycleRoot n ^ j.val)⁻¹ with hzdef
  have hzn : z ^ n = 1 := by
    rw [hzdef, mul_pow, hpow, inv_pow, hpow, inv_one, mul_one]
  have hterm : ∀ p : Fin n, (fourierMat n i p) * (fourierMatInv n p j) = (n:ℂ)⁻¹ * z ^ (p : ℕ) := by
    intro p
    simp only [fourierMat, fourierMatInv, Matrix.of_apply, hzdef, mul_pow]
    rw [pow_mul, mul_comm p.val j.val, pow_mul, ← inv_pow]
    ring
  rw [Finset.sum_congr rfl (fun p _ => hterm p), ← Finset.mul_sum, sum_pow_eq hzn]
  by_cases hij : i = j
  · have hz1 : z = 1 := by rw [hzdef, hij, mul_inv_cancel₀ (hne _)]
    rw [if_pos hz1, if_pos hij, inv_mul_cancel₀ hnC]
  · have hz1 : z ≠ 1 := by
      intro h
      rw [hzdef, mul_inv_eq_one₀ (hne _)] at h
      exact hij (Fin.ext ((cycleRoot_isPrimitiveRoot hn).pow_inj i.isLt j.isLt h))
    rw [if_neg hz1, if_neg hij, mul_zero]

/-- The columns of the discrete Fourier matrix diagonalise the cycle Laplacian. -/
lemma laplacian_mul_fourier {n : ℕ} (hn : 3 ≤ n) :
    cycleLaplacian n * fourierMat n
      = fourierMat n * Matrix.diagonal (fun j : Fin n => cycleEig n j.val) := by
  haveI : NeZero n := ⟨by omega⟩
  have hn0 : n ≠ 0 := by omega
  have hval1 : ((1 : Fin n) : ℕ) = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  have hval2 : (((1 : Fin n) + 1 : Fin n) : ℕ) = 2 := by
    rw [Fin.val_add, hval1, Nat.mod_eq_of_lt (by omega)]
  ext i j
  set y : ℂ := cycleRoot n ^ j.val with hy
  have hyn : y ^ n = 1 := by
    rw [hy, ← pow_mul, mul_comm, pow_mul, cycleRoot_pow_n hn0, one_pow]
  have hyne : y ≠ 0 := pow_ne_zero _ (cycleRoot_ne_zero n)
  have hF : ∀ p : Fin n, fourierMat n p j = y ^ (p : ℕ) := by
    intro p
    simp only [fourierMat, Matrix.of_apply, hy, ← pow_mul, mul_comm]
  have hshift : ∀ p : Fin n, y ^ ((p + 1 : Fin n) : ℕ) = y ^ (p : ℕ) * y := by
    intro p
    rw [Fin.val_add, hval1, pow_mod_of_pow_eq_one hyn, pow_succ]
  set b : Fin n := i + 1 with hb
  set c : Fin n := i - 1 with hc
  have hcb : c + 1 = i := sub_add_cancel i 1
  have hib : i ≠ b := by
    intro h
    have h1 : (1 : Fin n) = 0 := by
      have h2 := h.symm
      rw [hb] at h2
      exact add_left_cancel (a := i) (by rw [h2, add_zero])
    rw [← Fin.val_eq_val, hval1] at h1
    simp at h1
  have hic : i ≠ c := by
    intro h
    have h1 : (1 : Fin n) = 0 := sub_eq_self.mp h.symm
    rw [← Fin.val_eq_val, hval1] at h1
    simp at h1
  have hbc : b ≠ c := by
    intro h
    have h3 : i + ((1 : Fin n) + 1) = i := by rw [← add_assoc, ← hb, h, hcb]
    have h2 : ((1 : Fin n) + 1) = 0 := add_left_cancel (a := i) (by rw [h3, add_zero])
    rw [← Fin.val_eq_val, hval2] at h2
    simp at h2
  have hLi : cycleLaplacian n i i = 2 := by simp [cycleLaplacian]
  have hbval : (b : ℕ) = (i.val + 1) % n := by rw [hb, Fin.val_add, hval1]
  have hcval : ((c : ℕ) + 1) % n = i.val := by
    have h4 := congrArg Fin.val hcb
    rwa [Fin.val_add, hval1] at h4
  have hLb : cycleLaplacian n i b = -1 := by
    simp only [cycleLaplacian, Matrix.of_apply, if_neg hib]
    rw [if_pos (Or.inl hbval.symm)]
  have hLc : cycleLaplacian n i c = -1 := by
    simp only [cycleLaplacian, Matrix.of_apply, if_neg hic]
    rw [if_pos (Or.inr hcval)]
  have hzero : ∀ p : Fin n, p ≠ i → p ≠ b → p ≠ c → cycleLaplacian n i p = 0 := by
    intro p hpi hpb hpc
    simp only [cycleLaplacian, Matrix.of_apply, if_neg (Ne.symm hpi)]
    rw [if_neg]
    rintro (h | h)
    · exact hpb (Fin.ext (by rw [hbval, h]))
    · refine hpc (Fin.ext ?_)
      have hpi' : (p + 1 : Fin n) = i := Fin.ext (by rw [Fin.val_add, hval1, h])
      rw [hc, ← hpi']
      simp
  rw [Matrix.mul_diagonal, Matrix.mul_apply, hF i]
  have key : ∑ p : Fin n, cycleLaplacian n i p * fourierMat n p j
      = ∑ p ∈ ({i, b, c} : Finset (Fin n)), cycleLaplacian n i p * fourierMat n p j := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro p _ hp
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
    rw [hzero p hp.1 hp.2.1 hp.2.2, zero_mul]
  rw [key, Finset.sum_insert (by simp [hib, hic]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton, hLi, hLb, hLc, hF, hF, hF]
  have h1 : y ^ (b : ℕ) = y ^ (i : ℕ) * y := hshift i
  have h2 : y ^ (c : ℕ) * y = y ^ (i : ℕ) := by rw [← hshift c, hcb]
  have h3 : y ^ (c : ℕ) = y ^ (i : ℕ) * y⁻¹ := by
    field_simp
    linear_combination h2
  rw [h1, h3]
  simp only [cycleEig, ← hy]
  ring

lemma cycleEig_eq {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    cycleEig n k = ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ) := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  set t : ℝ := 2 * Real.pi * k / n with ht
  have hpow : cycleRoot n ^ k = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [cycleRoot, ← Complex.exp_nat_mul]
    congr 1
    rw [ht]
    push_cast
    field_simp
  rw [cycleEig, hpow, ← Complex.exp_neg]
  have hcos : Complex.cos (t : ℂ)
      = (Complex.exp ((t:ℂ) * Complex.I) + Complex.exp (-((t:ℂ) * Complex.I))) / 2 := by
    rw [Complex.cos]; ring_nf
  push_cast [Complex.ofReal_cos]
  rw [hcos]
  ring

lemma fourierMat_apply_exp {n : ℕ} (hn : n ≠ 0) (i j : Fin n) :
    fourierMat n i j = Complex.exp (2 * Real.pi * Complex.I * i * j / n) := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [fourierMat, Matrix.of_apply, cycleRoot, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- The discrete Fourier vectors `v k (j) = exp (2 π I k j / n)` are eigenvectors of the cycle
Laplacian, with eigenvalue `2 - 2 cos (2 π k / n)`. -/
theorem cycleLaplacian_mulVec_fourierVec (n : ℕ) (hn : 3 ≤ n) (k : Fin n) :
    cycleLaplacian n *ᵥ (fun j : Fin n => Complex.exp (2 * Real.pi * Complex.I * k * j / n))
      = ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ) •
        (fun j : Fin n => Complex.exp (2 * Real.pi * Complex.I * k * j / n)) := by
  have hn0 : n ≠ 0 := by omega
  have hv : ∀ j : Fin n,
      Complex.exp (2 * Real.pi * Complex.I * k * j / n) = fourierMat n j k := by
    intro j
    rw [fourierMat_apply_exp hn0]
    ring_nf
  funext i
  have h := congrFun (congrFun (laplacian_mul_fourier hn) i) k
  rw [Matrix.mul_apply, Matrix.mul_diagonal, cycleEig_eq hn0] at h
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hv]
  rw [h, mul_comm]

/-- **Spectrum of the cycle Laplacian.**  For `n ≥ 3` the eigenvalues of the Laplacian of the
cycle graph `C n` are exactly the numbers `2 - 2 cos (2 π k / n)` for `k = 0, …, n - 1`. -/
theorem cycle_laplacian_spectrum (n : ℕ) (hn : 3 ≤ n) :
    spectrum ℂ (cycleLaplacian n) =
      (fun k : ℕ => ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ)) '' (Finset.range n) := by
  have hn0 : n ≠ 0 := by omega
  have hFG := fourier_mul_inv hn0
  have hL : cycleLaplacian n
      = fourierMat n * Matrix.diagonal (fun j : Fin n => cycleEig n j.val) * fourierMatInv n := by
    rw [← laplacian_mul_fourier hn, Matrix.mul_assoc, hFG, Matrix.mul_one]
  have hdetFG : (fourierMat n).det * (fourierMatInv n).det = 1 := by
    rw [← Matrix.det_mul, hFG, Matrix.det_one]
  ext μ
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
  have hsub : algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) μ - cycleLaplacian n
      = fourierMat n * Matrix.diagonal (fun j : Fin n => μ - cycleEig n j.val)
          * fourierMatInv n := by
    rw [hL, ← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul, ← smul_one_eq_diagonal,
      Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hFG,
      Algebra.algebraMap_eq_smul_one]
  rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  have hre : ((fourierMat n).det * ∏ j : Fin n, (μ - cycleEig n j.val)) * (fourierMatInv n).det
      = (∏ j : Fin n, (μ - cycleEig n j.val)) * ((fourierMat n).det * (fourierMatInv n).det) := by
    ring
  rw [hre, hdetFG, mul_one, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨a, -, ha⟩
    refine ⟨a.val, by simp [a.isLt], ?_⟩
    simp only
    rw [← cycleEig_eq hn0]
    exact (sub_eq_zero.mp ha).symm
  · rintro ⟨k, hk, hkμ⟩
    simp only [Finset.coe_range, Set.mem_Iio] at hk
    simp only at hkμ
    refine ⟨⟨k, hk⟩, Finset.mem_univ _, ?_⟩
    show μ - cycleEig n k = 0
    rw [cycleEig_eq hn0, hkμ, sub_self]

end Frontier.Spectral

