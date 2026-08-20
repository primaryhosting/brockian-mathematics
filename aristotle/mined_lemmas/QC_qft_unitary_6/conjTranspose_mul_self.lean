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

lemma conjTranspose_mul_self (N : ℕ) (hN : 0 < N) :
    (qftMatrix N)ᴴ * qftMatrix N = 1 := by
  ext j k
  rw [Matrix.mul_apply]
  have key : ∀ l : Fin N, (qftMatrix N)ᴴ j l * qftMatrix N l k
      = ((N : ℂ))⁻¹ * zeta N (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ^ (l : ℕ) := by
    intro l
    rw [Matrix.conjTranspose_apply, qftMatrix_apply, qftMatrix_apply, Complex.star_def,
      map_mul, zeta_conj]
    have hr : (starRingEnd ℂ) ((Real.sqrt N : ℝ) : ℂ)⁻¹ = ((Real.sqrt N : ℝ) : ℂ)⁻¹ := by
      simp [← Complex.ofReal_inv]
    rw [hr, zeta_pow]
    rw [mul_mul_mul_comm, inv_sqrt_sq hN, ← zeta_add]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun l _ => key l)]
  rw [← Finset.mul_sum]
  have : ∑ l : Fin N, zeta N (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ^ (l : ℕ)
      = ∑ l ∈ Finset.range N, zeta N (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ^ l :=
    Fin.sum_univ_eq_sum_range (fun l => zeta N (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ^ l) N
  rw [this]
  have hlt : (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ)).natAbs < N := by
    have hk := k.isLt
    have hj := j.isLt
    omega
  rw [sum_zeta_pow hlt]
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  by_cases hjk : j = k
  · subst hjk
    simp [hNc]
  · have : (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ≠ 0 := by
      simp only [sub_ne_zero]
      intro h
      exact hjk (Fin.ext (by exact_mod_cast h.symm))
    rw [if_neg this]
    simp [hjk]

