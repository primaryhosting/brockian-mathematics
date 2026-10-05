/-!
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Statement: The 7-qubit QFT matrix is unitary.
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

open Finset

/-- The `N`-dimensional discrete Fourier transform (quantum Fourier transform) matrix:
its `(j, k)` entry is `exp (2 π i j k / N) / √N`.  For `n` qubits one takes `N = 2 ^ n`. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun j k => Complex.exp (2 * Real.pi * Complex.I * (j.val * k.val) / N) / Real.sqrt N

/-- Geometric sum of `N`-th roots of unity: `∑_{k<N} exp (2 π i a k / N)` equals `N` when
`N ∣ a` and `0` otherwise. -/
theorem sum_exp_int (N : ℕ) (hN : 0 < N) (a : ℤ) :
    ∑ k : Fin N, Complex.exp (2 * Real.pi * Complex.I * a * k.val / N)
      = if (N : ℤ) ∣ a then (N : ℂ) else 0 := by
  have hprim := Complex.isPrimitiveRoot_exp N hN.ne'
  set ξ : ℂ := Complex.exp (2 * Real.pi * Complex.I / N) with hxi
  set w : ℂ := ξ ^ (a : ℤ) with hw
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hterm : ∀ k : Fin N, Complex.exp (2 * Real.pi * Complex.I * a * k.val / N)
      = w ^ (k.val) := by
    intro k
    rw [hw, hxi, ← Complex.exp_int_mul, ← Complex.exp_nat_mul]
    congr 1
    field_simp
  rw [Finset.sum_congr rfl (fun k _ => hterm k),
    Fin.sum_univ_eq_sum_range (fun i => w ^ i) N]
  have hwN : w ^ N = 1 := by
    rw [hw, ← zpow_natCast (ξ ^ (a : ℤ)) N, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hprim.pow_eq_one, one_zpow]
  by_cases h : (N : ℤ) ∣ a
  · have hw1 : w = 1 := (hprim.zpow_eq_one_iff_dvd a).mpr h
    simp [hw1, h]
  · have hw1 : w ≠ 1 := fun hc => h ((hprim.zpow_eq_one_iff_dvd a).mp hc)
    rw [geom_sum_eq hw1, hwN, if_neg h]
    simp

/-- The `N`-dimensional discrete Fourier transform matrix is unitary, for any `N > 0`. -/
theorem qft_unitary (N : ℕ) (hN : 0 < N) : qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hsq : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp
  rw [Matrix.mem_unitaryGroup_iff]
  ext l j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have key : ∀ k : Fin N, qftMatrix N l k * (star (qftMatrix N)) k j
      = Complex.exp (2 * Real.pi * Complex.I * (((l : ℤ) - (j : ℤ) : ℤ) : ℂ) * k.val / N)
        / N := by
    intro k
    simp only [qftMatrix, Matrix.star_apply, Complex.star_def]
    rw [map_div₀, ← Complex.exp_conj, Complex.conj_ofReal]
    rw [show (starRingEnd ℂ) (2 * Real.pi * Complex.I * (j.val * k.val) / N)
        = -(2 * Real.pi * Complex.I * (j.val * k.val) / N) by
      simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal,
        Complex.conj_natCast, map_ofNat]
      ring]
    rw [div_mul_div_comm, ← Complex.exp_add, hsq]
    congr 1
    push_cast
    field_simp
    ring_nf
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.sum_div,
    sum_exp_int N hN ((l : ℤ) - (j : ℤ))]
  by_cases h : l = j
  · simp [h, hN0]
  · rw [if_neg h, if_neg, zero_div]
    intro hd
    apply h
    have hz : ((l : ℤ) - (j : ℤ)) = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd hd ?_
      have h1 := l.isLt
      have h2 := j.isLt
      rw [abs_lt]
      omega
    exact Fin.ext (by omega)

/-- **The 7-qubit quantum Fourier transform matrix is unitary.** -/
theorem qft_unitary_7 : qftMatrix (2 ^ 7) ∈ Matrix.unitaryGroup (Fin (2 ^ 7)) ℂ :=
  qft_unitary _ (by positivity)

end QC

