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
