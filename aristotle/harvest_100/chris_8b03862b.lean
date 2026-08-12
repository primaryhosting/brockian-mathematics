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

namespace QC

/-- The primitive `N`-th root of unity `exp (2 π i / N)`. -/
noncomputable def zeta (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/-- The `N × N` quantum Fourier transform matrix,
with entries `N ^ (-1/2) * exp (2 π i j k / N)`. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k =>
    ((Real.sqrt N : ℝ) : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I * (j * k) / N)

/-- The quantum Fourier transform on `n` qubits, a `2 ^ n × 2 ^ n` matrix. -/
noncomputable def qft (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := qftMatrix (2 ^ n)

lemma zeta_isPrimitiveRoot {N : ℕ} (hN : N ≠ 0) : IsPrimitiveRoot (zeta N) N :=
  Complex.isPrimitiveRoot_exp N hN

lemma qftMatrix_apply (N : ℕ) (j k : Fin N) :
    qftMatrix N j k = ((Real.sqrt N : ℝ) : ℂ)⁻¹ * zeta N ^ ((j : ℕ) * (k : ℕ)) := by
  have h : (2 : ℂ) * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ)) / N
      = (((j : ℕ) * (k : ℕ) : ℕ) : ℂ) * (2 * Real.pi * Complex.I / N) := by
    push_cast; ring
  simp only [qftMatrix, Matrix.of_apply, zeta, h, Complex.exp_nat_mul]

lemma conj_zeta (N : ℕ) : (starRingEnd ℂ) (zeta N) = (zeta N)⁻¹ := by
  rw [zeta, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [Complex.ext_iff]
  ring

/-- Character-sum lemma: the sum of `(ζ ^ m) ^ k` over `k < N`. -/
lemma sum_zeta_zpow {N : ℕ} (hN : N ≠ 0) (m : ℤ) :
    ∑ k ∈ Finset.range N, (zeta N ^ m) ^ k = if (N : ℤ) ∣ m then (N : ℂ) else 0 := by
  have hprim := zeta_isPrimitiveRoot hN
  by_cases hdvd : (N : ℤ) ∣ m
  · have h1 : zeta N ^ m = 1 := (hprim.zpow_eq_one_iff_dvd m).mpr hdvd
    simp [h1, hdvd]
  · have h1 : zeta N ^ m ≠ 1 := fun h => hdvd ((hprim.zpow_eq_one_iff_dvd m).mp h)
    have hpowN : (zeta N ^ m) ^ N = 1 := by
      rw [← zpow_natCast (zeta N ^ m) N, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hprim.pow_eq_one, one_zpow]
    rw [geom_sum_eq h1 N, hpowN]
    simp [hdvd]

lemma sq_inv_sqrt (N : ℕ) :
    ((Real.sqrt N : ℝ) : ℂ)⁻¹ * ((Real.sqrt N : ℝ) : ℂ)⁻¹ = ((N : ℂ))⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, ← Real.sqrt_mul_self (by positivity : (0:ℝ) ≤ (N:ℝ))]
  norm_num

/-- The `N × N` QFT matrix is unitary. -/
theorem qftMatrix_unitary {N : ℕ} (hN : N ≠ 0) :
    qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  have hzne : zeta N ≠ 0 := by
    simp [zeta, Complex.exp_ne_zero]
  have key : ∀ k : Fin N,
      qftMatrix N i k * (star (qftMatrix N) : Matrix (Fin N) (Fin N) ℂ) k j
        = ((N : ℂ))⁻¹ * (zeta N ^ ((i : ℤ) - (j : ℤ))) ^ (k : ℕ) := by
    intro k
    have hstar : (star (qftMatrix N) : Matrix (Fin N) (Fin N) ℂ) k j
        = (starRingEnd ℂ) (qftMatrix N j k) := rfl
    rw [hstar, qftMatrix_apply, qftMatrix_apply]
    simp only [map_mul, map_pow, conj_zeta, map_inv₀, Complex.conj_ofReal]
    have h1 : ((zeta N)⁻¹ : ℂ) ^ ((j : ℕ) * (k : ℕ)) = zeta N ^ (-((j : ℤ) * (k : ℤ))) := by
      rw [zpow_neg, ← inv_zpow, ← zpow_natCast ((zeta N)⁻¹) ((j : ℕ) * (k : ℕ))]
      push_cast
      ring_nf
    have h2 : (zeta N : ℂ) ^ ((i : ℕ) * (k : ℕ)) = zeta N ^ (((i : ℤ) * (k : ℤ))) := by
      rw [← zpow_natCast (zeta N) ((i : ℕ) * (k : ℕ))]
      push_cast
      ring_nf
    rw [h1, h2, ← zpow_natCast (zeta N ^ ((i : ℤ) - (j : ℤ))) (k : ℕ), ← zpow_mul]
    rw [show ((i : ℤ) * (k : ℤ)) = ((i:ℤ) * k) from rfl]
    rw [mul_mul_mul_comm, sq_inv_sqrt, ← zpow_add₀ hzne]
    congr 2
    ring
  have hsum : (qftMatrix N * star (qftMatrix N)) i j
      = ((N : ℂ))⁻¹ * ∑ k ∈ Finset.range N, (zeta N ^ ((i : ℤ) - (j : ℤ))) ^ k := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_congr rfl (fun k _ => key k)]
    rw [← Finset.mul_sum]
    congr 1
    exact (Fin.sum_univ_eq_sum_range (fun k => (zeta N ^ ((i : ℤ) - (j : ℤ))) ^ k) N)
  rw [hsum, sum_zeta_zpow hN]
  by_cases hij : i = j
  · subst hij
    have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    have hd : ((N : ℤ)) ∣ ((i : ℤ) - (i : ℤ)) := by simp
    simp only [sub_self, dvd_zero, if_true, Matrix.one_apply_eq]
    field_simp
  · have hnd : ¬ ((N : ℤ) ∣ ((i : ℤ) - (j : ℤ))) := by
      intro h
      have hi : ((i : ℕ) : ℤ) < (N : ℤ) := by exact_mod_cast i.isLt
      have hj : ((j : ℕ) : ℤ) < (N : ℤ) := by exact_mod_cast j.isLt
      have hi0 : (0 : ℤ) ≤ ((i : ℕ) : ℤ) := Int.natCast_nonneg _
      have hj0 : (0 : ℤ) ≤ ((j : ℕ) : ℤ) := Int.natCast_nonneg _
      have hne : ((i : ℤ) - (j : ℤ)) ≠ 0 := by
        have hne' : (i : ℕ) ≠ (j : ℕ) := fun hc => hij (Fin.ext hc)
        omega
      have hle : (N : ℤ) ≤ |((i : ℤ) - (j : ℤ))| :=
        Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr h)
      rcases abs_cases ((i : ℤ) - (j : ℤ)) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hle <;> omega
    simp [hnd, Matrix.one_apply_ne hij]

/-- The 5-qubit quantum Fourier transform matrix is unitary. -/
theorem qft_unitary_5 : qft 5 ∈ Matrix.unitaryGroup (Fin (2 ^ 5)) ℂ :=
  qftMatrix_unitary (by norm_num)

end QC

#print axioms QC.qft_unitary_5

