/-
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Complex Matrix Finset

namespace QC

/-- The `n × n` quantum Fourier transform matrix: the entry at `(j, k)` is
`ω^(j*k) / √n`, where `ω = exp(2πi/n)` is a primitive `n`-th root of unity. -/

theorem qft_mul_conjTranspose (n : ℕ) (hn : n ≠ 0) :
    (qftMatrix n) * (qftMatrix n)ᴴ = 1 := by
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / n)) n :=
    Complex.isPrimitiveRoot_exp n hn
  set ζ := Complex.exp (2 * Real.pi * Complex.I / n) with hζdef
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hnorm : ‖ζ‖ = 1 := by rw [hζdef, Complex.norm_exp]; simp
  have hζ0 : ζ ≠ 0 := by intro h; rw [h] at hnorm; simp at hnorm
  have hconj : (starRingEnd ℂ) ζ = ζ⁻¹ := (Complex.inv_eq_conj hnorm).symm
  have hsqrt : ((Real.sqrt n : ℝ) : ℂ) * ((Real.sqrt n : ℝ) : ℂ) = (n : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]; simp
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  -- Each summand is `ζ^(j-k)` raised to the power `l`, divided by `n`.
  have hterm : ∀ l : Fin n, qftMatrix n j l * (qftMatrix n)ᴴ l k
      = (ζ ^ ((j : ℤ) - (k : ℤ))) ^ (l : ℕ) / (n : ℂ) := by
    intro l
    simp only [qftMatrix, Matrix.conjTranspose_apply, star_div₀, star_pow, Complex.star_def,
      hconj, Complex.conj_ofReal, ← hζdef]
    rw [div_mul_div_comm, hsqrt]
    congr 1
    rw [← zpow_natCast ζ ((j : ℕ) * (l : ℕ)), ← zpow_natCast ζ⁻¹ ((k : ℕ) * (l : ℕ)),
      _root_.inv_zpow, ← _root_.zpow_neg, ← zpow_natCast (ζ ^ ((j : ℤ) - k)) (l : ℕ),
      ← _root_.zpow_mul, ← zpow_add₀ hζ0]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun l _ => hterm l), ← Finset.sum_div]
  by_cases hjk : j = k
  · -- Diagonal entries: the geometric sum has `n` terms, each equal to `1`.
    subst hjk
    simp only [sub_self, zpow_zero, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, if_pos]
    rw [div_self hn0]
  · -- Off-diagonal entries: a nontrivial geometric sum of `n`-th roots of unity vanishes.
    rw [if_neg hjk]
    have hne : ((j : ℤ) - (k : ℤ)) ≠ 0 := by
      simp only [sub_ne_zero, ne_eq, Nat.cast_inj]
      exact fun h => hjk (Fin.ext h)
    have hξ1 : ζ ^ ((j : ℤ) - (k : ℤ)) ≠ 1 := by
      rw [Ne, hprim.zpow_eq_one_iff_dvd]
      intro hdvd
      refine hne (Int.eq_zero_of_abs_lt_dvd hdvd ?_)
      have hj := j.isLt
      have hk := k.isLt
      rw [abs_lt]
      omega
    have hξn : (ζ ^ ((j : ℤ) - (k : ℤ))) ^ n = 1 := by
      rw [← zpow_natCast (ζ ^ ((j : ℤ) - (k : ℤ))) n, ← _root_.zpow_mul, mul_comm,
        _root_.zpow_mul, zpow_natCast, hprim.pow_eq_one, _root_.one_zpow]
    rw [Fin.sum_univ_eq_sum_range (fun i => (ζ ^ ((j : ℤ) - (k : ℤ))) ^ i) n,
      geom_sum_eq hξ1, hξn, sub_self, zero_div, zero_div]

/-- The `8 × 8` quantum Fourier transform matrix is unitary. -/
