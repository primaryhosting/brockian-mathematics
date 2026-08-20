import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

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

/-- `QC.zeta N m = exp (2 π i m / N)`, the `m`-th power of the primitive `N`-th root of unity
used to define the quantum Fourier transform. -/

lemma sum_zeta_pow {N : ℕ} {m : ℤ} (hm : m.natAbs < N) :
    ∑ l ∈ Finset.range N, zeta N m ^ l = if m = 0 then (N : ℂ) else 0 := by
  by_cases h : m = 0
  · subst h
    simp [zeta_zero]
  · rw [if_neg h]
    have hne : zeta N m ≠ 1 := zeta_ne_one h hm
    rw [geom_sum_eq hne]
    have hpow : zeta N m ^ N = 1 := by
      rw [zeta_pow, zeta]
      rw [Complex.exp_eq_one_iff]
      refine ⟨m, ?_⟩
      have hN : (0:ℕ) < N := lt_of_le_of_lt (Nat.zero_le _) hm
      have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
      field_simp
      push_cast
      ring
    rw [hpow]
    simp

