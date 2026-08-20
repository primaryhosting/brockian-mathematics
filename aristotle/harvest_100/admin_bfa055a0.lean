import Mathlib

/-!
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Finset Matrix

/-- The primitive `n`-th root of unity `exp(2πi/n)` used in the quantum Fourier transform. -/
noncomputable def qftOmega (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

/-- The `n`-dimensional quantum Fourier transform matrix,
`F j k = ω^(j*k) / √n` with `ω = exp(2πi/n)`. -/
noncomputable def qftMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => qftOmega n ^ (j.val * k.val) / (Real.sqrt n : ℝ)

private lemma zeta_prim : IsPrimitiveRoot (qftOmega 64) 64 := by
  have := Complex.isPrimitiveRoot_exp 64 (by norm_num)
  simpa [qftOmega] using this

private lemma zeta_ne_zero : qftOmega 64 ≠ 0 := by
  simp [qftOmega, Complex.exp_ne_zero]

private lemma norm_zeta : ‖qftOmega 64‖ = 1 := zeta_prim.norm'_eq_one (by norm_num)

private lemma conj_zeta : (starRingEnd ℂ) (qftOmega 64) = (qftOmega 64)⁻¹ :=
  (Complex.inv_eq_conj norm_zeta).symm

/-- Geometric sum of the powers of `ζ^d` over a full period vanishes when `64 ∤ d`. -/
private lemma sum_zpow_eq_zero (d : ℤ) (h : ¬ ((64 : ℤ) ∣ d)) :
    ∑ k : Fin 64, (qftOmega 64 ^ d) ^ (k : ℕ) = 0 := by
  set η : ℂ := qftOmega 64 ^ d with hη
  have hne : η ≠ 1 := by
    rw [hη]
    intro hc
    exact h ((zeta_prim.zpow_eq_one_iff_dvd d).mp hc)
  have hpow : η ^ 64 = 1 := by
    rw [hη, ← zpow_natCast (qftOmega 64 ^ d) 64, ← _root_.zpow_mul]
    rw [zeta_prim.zpow_eq_one_iff_dvd]
    exact ⟨d, by ring⟩
  have : ∑ k ∈ Finset.range 64, η ^ k = (η ^ 64 - 1) / (η - 1) := geom_sum_eq hne 64
  rw [Fin.sum_univ_eq_sum_range (fun k => η ^ k) 64, this, hpow]
  simp

/-- The 6-qubit (64-dimensional) quantum Fourier transform matrix is unitary. -/
theorem qft_unitary_6 : qftMatrix 64 ∈ unitary (Matrix (Fin 64) (Fin 64) ℂ) := by
  have hs : ((Real.sqrt 64 : ℝ) : ℂ) = 8 := by
    have : Real.sqrt 64 = 8 := by
      rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [this]; norm_num
  have key : (qftMatrix 64)ᴴ * qftMatrix 64 = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    have hterm : ∀ k : Fin 64,
        (qftMatrix 64)ᴴ i k * qftMatrix 64 k j
          = (qftOmega 64 ^ ((j : ℤ) - (i : ℤ))) ^ (k : ℕ) / 64 := by
      intro k
      simp only [Matrix.conjTranspose_apply, qftMatrix, Nat.cast_ofNat, hs, Complex.star_def]
      rw [map_div₀, map_pow, conj_zeta]
      rw [← zpow_natCast (qftOmega 64)⁻¹ (k.val * i.val),
        ← zpow_natCast (qftOmega 64) (k.val * j.val),
        ← zpow_natCast (qftOmega 64 ^ ((j : ℤ) - (i : ℤ))) k.val,
        ← _root_.zpow_mul, _root_.inv_zpow, ← _root_.zpow_neg]
      rw [show ((starRingEnd ℂ) (8 : ℂ)) = 8 from Complex.conj_eq_iff_re.mpr rfl]
      rw [div_mul_div_comm, ← zpow_add₀ zeta_ne_zero]
      congr 1
      · congr 1; push_cast; ring
      · norm_num
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    rw [← Finset.sum_div]
    by_cases hij : i = j
    · subst hij
      simp only [sub_self, zpow_zero, one_pow, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, Matrix.one_apply_eq]
      norm_num
    · have hd : ¬ ((64 : ℤ) ∣ ((j : ℤ) - (i : ℤ))) := by
        intro hdvd
        have h1 : (i : ℤ) < 64 := by exact_mod_cast i.isLt
        have h2 : (j : ℤ) < 64 := by exact_mod_cast j.isLt
        have h3 : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg _
        have h4 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg _
        have : (j : ℤ) - (i : ℤ) = 0 := by omega
        exact hij (Fin.ext (by omega))
      rw [sum_zpow_eq_zero _ hd]
      rw [Matrix.one_apply_ne hij]
      simp
  refine ⟨key, ?_⟩
  have := mul_eq_one_comm.mp key
  simpa using this

end QC

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

