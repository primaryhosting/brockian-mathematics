import Mathlib

/-!
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
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

namespace QC

/-- The primitive `N`-th root of unity `exp (2 π i / N)`. -/
noncomputable def omega (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/-- The `n`-qubit quantum Fourier transform matrix, of size `2^n × 2^n`:
`F j k = (1 / √(2^n)) * exp (2 π i j k / 2^n)`. -/
noncomputable def qft (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  fun j k => ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ * omega (2 ^ n) ^ (j.val * k.val)

lemma omega_isPrimitiveRoot (N : ℕ) (hN : N ≠ 0) : IsPrimitiveRoot (omega N) N :=
  Complex.isPrimitiveRoot_exp N hN

lemma omega_ne_zero (N : ℕ) : omega N ≠ 0 := Complex.exp_ne_zero _

lemma conj_omega (N : ℕ) : (starRingEnd ℂ) (omega N) = (omega N)⁻¹ := by
  rw [omega, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [Complex.ext_iff]
  ring

lemma omega_zpow_sub (N j k l : ℕ) :
    ((omega N)⁻¹) ^ (k * j) * (omega N) ^ (k * l)
      = ((omega N) ^ ((l : ℤ) - (j : ℤ))) ^ k := by
  have h0 : omega N ≠ 0 := omega_ne_zero N
  have hinv : ((omega N)⁻¹) ^ (k * j) = (omega N) ^ (-((k * j : ℕ) : ℤ)) := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [hinv, ← zpow_natCast (omega N) (k * l), ← zpow_add₀ h0,
    ← zpow_natCast ((omega N) ^ ((l : ℤ) - (j : ℤ))) k, ← zpow_mul]
  congr 1
  push_cast
  ring

lemma sum_omega_zpow_eq_zero (N : ℕ) (hN : N ≠ 0) (m : ℤ) (hm : ¬ ((N : ℤ) ∣ m)) :
    ∑ _k : Fin N, ((omega N) ^ m) ^ ((_k : Fin N) : ℕ) = 0 := by
  have hprim := omega_isPrimitiveRoot N hN
  have hne : (omega N) ^ m ≠ 1 := by
    intro h
    exact hm ((hprim.zpow_eq_one_iff_dvd m).mp h)
  have hpow : ((omega N) ^ m) ^ N = 1 := by
    rw [← zpow_natCast ((omega N) ^ m) N, ← zpow_mul, mul_comm, zpow_mul,
      hprim.zpow_eq_one, one_zpow]
  rw [Fin.sum_univ_eq_sum_range (fun k => ((omega N) ^ m) ^ k) N, geom_sum_eq hne, hpow]
  simp

/-- The `n`-qubit quantum Fourier transform matrix is unitary. -/
theorem qft_unitary (n : ℕ) : qft n ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  have hN : (2 ^ n : ℕ) ≠ 0 := by positivity
  set c : ℂ := ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ with hc
  have hsq : ((Real.sqrt (2 ^ n) : ℝ) : ℂ) * ((Real.sqrt (2 ^ n) : ℝ) : ℂ) = ((2 ^ n : ℕ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity : (0:ℝ) ≤ 2 ^ n)]
    push_cast
    ring
  have hcc : c * c = ((2 ^ n : ℕ) : ℂ)⁻¹ := by
    rw [hc, ← mul_inv, hsq]
  rw [Matrix.mem_unitaryGroup_iff']
  ext j l
  have key : ∀ k : Fin (2 ^ n),
      (star (qft n)) j k * qft n k l
        = (c * c) * ((omega (2 ^ n) ^ ((l : ℤ) - (j : ℤ))) ^ (k : ℕ)) := by
    intro k
    have hs : (star (qft n)) j k = c * ((omega (2 ^ n))⁻¹) ^ (k.val * j.val) := by
      rw [Matrix.star_apply, qft]
      simp only [star_mul', star_pow, ← conj_omega]
      rw [hc]
      simp [Complex.conj_ofReal, mul_comm]
    rw [hs, qft]
    rw [show c * (omega (2 ^ n))⁻¹ ^ (k.val * j.val) * (c * omega (2 ^ n) ^ (k.val * l.val))
        = (c * c) * ((omega (2 ^ n))⁻¹ ^ (k.val * j.val) * omega (2 ^ n) ^ (k.val * l.val)) by
      ring]
    rw [omega_zpow_sub]
  rw [Matrix.mul_apply, Finset.sum_congr rfl (fun k _ => key k), ← Finset.mul_sum,
    Matrix.one_apply]
  by_cases h : j = l
  · subst h
    simp only [sub_self, zpow_zero, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hcc]
    field_simp
    simp
  · rw [if_neg h]
    have hdvd : ¬ ((2 ^ n : ℕ) : ℤ) ∣ ((l : ℤ) - (j : ℤ)) := by
      intro hd
      have hlt : |((l : ℤ) - (j : ℤ))| < ((2 ^ n : ℕ) : ℤ) := by
        have hj : (j : ℤ) < ((2 ^ n : ℕ) : ℤ) := by exact_mod_cast j.isLt
        have hl : (l : ℤ) < ((2 ^ n : ℕ) : ℤ) := by exact_mod_cast l.isLt
        have hj0 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg _
        have hl0 : (0 : ℤ) ≤ (l : ℤ) := Int.natCast_nonneg _
        rw [abs_lt]
        omega
      have := Int.eq_zero_of_abs_lt_dvd hd hlt
      exact absurd (Fin.ext (by exact_mod_cast (by omega : (j : ℤ) = (l : ℤ)))) h
    rw [sum_omega_zpow_eq_zero (2 ^ n) hN _ hdvd, mul_zero]

/-- Unitarity of the QFT, spelled out: `Fᴴ * F = 1`. -/
theorem qft_conjTranspose_mul_self (n : ℕ) : Matrix.conjTranspose (qft n) * qft n = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp (qft_unitary n)

/-- Unitarity of the QFT, spelled out: `F * Fᴴ = 1`. -/
theorem qft_mul_conjTranspose_self (n : ℕ) : qft n * Matrix.conjTranspose (qft n) = 1 :=
  Matrix.mem_unitaryGroup_iff.mp (qft_unitary n)

end QC

