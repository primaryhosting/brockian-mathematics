/-!
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Statement: The 8-qubit QFT matrix is unitary.
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

open Complex

/-- The primitive `n`-th root of unity `exp (2πi / n)` used by the discrete Fourier transform. -/
noncomputable def omega (n : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))

/-- The `n`-dimensional quantum Fourier transform matrix:
`QFT j k = ω^(j*k) / √n` with `ω = exp (2πi/n)`. -/
noncomputable def qftMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => ((Real.sqrt n : ℝ) : ℂ)⁻¹ * omega n ^ ((j : ℕ) * (k : ℕ))

lemma omega_ne_zero (n : ℕ) : omega n ≠ 0 := Complex.exp_ne_zero _

lemma isPrimitiveRoot_omega (n : ℕ) (hn : n ≠ 0) : IsPrimitiveRoot (omega n) n :=
  Complex.isPrimitiveRoot_exp n hn

lemma conj_omega (n : ℕ) : (starRingEnd ℂ) (omega n) = (omega n)⁻¹ := by
  rw [omega, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  rw [map_div₀, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_natCast,
    map_ofNat]
  ring

lemma omega_inv_pow_mul (n a b c : ℕ) :
    ((omega n)⁻¹) ^ (a * b) * omega n ^ (a * c) = (omega n ^ ((c : ℤ) - (b : ℤ))) ^ a := by
  have hne : omega n ≠ 0 := omega_ne_zero n
  rw [inv_pow, ← zpow_natCast (omega n) (a * b), ← zpow_natCast (omega n) (a * c),
    ← zpow_natCast (omega n ^ ((c : ℤ) - (b : ℤ))) a, ← zpow_neg, ← zpow_add₀ hne, ← zpow_mul]
  congr 1
  push_cast
  ring

/-- The geometric sum of the powers of `ω^d` vanishes when `n` does not divide `d`. -/
lemma sum_omega_zpow_eq_zero (n : ℕ) (hn : n ≠ 0) (d : ℤ) (hd : ¬ ((n : ℤ) ∣ d)) :
    ∑ i ∈ Finset.range n, (omega n ^ d) ^ i = 0 := by
  have hprim : IsPrimitiveRoot (omega n) n := isPrimitiveRoot_omega n hn
  have hne : omega n ^ d ≠ 1 := fun h => hd ((hprim.zpow_eq_one_iff_dvd d).mp h)
  have hpow : (omega n ^ d) ^ n = 1 := by
    rw [← zpow_natCast (omega n ^ d) n, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      hprim.pow_eq_one, one_zpow]
  rw [geom_sum_eq hne, hpow, sub_self, zero_div]

/-- The `n`-dimensional QFT matrix is unitary, for every `n ≠ 0`. -/
theorem qft_unitary (n : ℕ) (hn : n ≠ 0) : qftMatrix n ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hsqrt : ((Real.sqrt n : ℝ) : ℂ)⁻¹ * ((Real.sqrt n : ℝ) : ℂ)⁻¹ = ((n : ℂ))⁻¹ := by
    have h : ((Real.sqrt n : ℝ) : ℂ) * ((Real.sqrt n : ℝ) : ℂ) = (n : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hnpos.le]
      simp
    rw [← mul_inv, h]
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  have key : ∀ i : Fin n, (star (qftMatrix n)) j i * qftMatrix n i k
      = ((n : ℂ))⁻¹ * (omega n ^ ((k : ℤ) - (j : ℤ))) ^ (i : ℕ) := by
    intro i
    rw [Matrix.star_apply]
    show (starRingEnd ℂ) (qftMatrix n i j) * qftMatrix n i k = _
    rw [qftMatrix, qftMatrix]
    simp only [map_mul, map_pow, conj_omega, map_inv₀, Complex.conj_ofReal]
    rw [show ((Real.sqrt n : ℝ) : ℂ)⁻¹ * (omega n)⁻¹ ^ ((i : ℕ) * (j : ℕ)) *
        (((Real.sqrt n : ℝ) : ℂ)⁻¹ * omega n ^ ((i : ℕ) * (k : ℕ)))
        = (((Real.sqrt n : ℝ) : ℂ)⁻¹ * ((Real.sqrt n : ℝ) : ℂ)⁻¹) *
          ((omega n)⁻¹ ^ ((i : ℕ) * (j : ℕ)) * omega n ^ ((i : ℕ) * (k : ℕ))) by ring]
    rw [hsqrt]
    congr 1
    exact omega_inv_pow_mul n (i : ℕ) (j : ℕ) (k : ℕ)
  rw [Finset.sum_congr rfl (fun i _ => key i), ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun i => (omega n ^ ((k : ℤ) - (j : ℤ))) ^ i) n]
  by_cases h : j = k
  · subst h
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simp only [sub_self, zpow_zero, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one, if_true]
    field_simp
  · have hd : ¬ ((n : ℤ) ∣ ((k : ℤ) - (j : ℤ))) := by
      intro hdvd
      have hjk : (j : ℕ) < n := j.isLt
      have hkn : (k : ℕ) < n := k.isLt
      have habs : |(k : ℤ) - (j : ℤ)| < (n : ℤ) := by
        rw [abs_lt]; omega
      have := Int.eq_zero_of_abs_lt_dvd hdvd habs
      exact h (Fin.ext (by omega))
    rw [sum_omega_zpow_eq_zero n hn _ hd, mul_zero, if_neg h]

/-- The 8-qubit quantum Fourier transform matrix (dimension `2^8 = 256`) is unitary. -/
theorem qft_unitary_8 : qftMatrix (2 ^ 8) ∈ Matrix.unitaryGroup (Fin (2 ^ 8)) ℂ :=
  qft_unitary (2 ^ 8) (by norm_num)

end QC

#print axioms QC.qft_unitary_8

