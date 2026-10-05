/-!
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
Verification: pending
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

/-- The `N`-th root of unity `exp (2 π i / N)`. -/

theorem qft_unitary (N : ℕ) (hN : N ≠ 0) : qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext k l
  have hNpos : (0 : ℝ) < N := by positivity
  have hsqrt : ((Real.sqrt N : ℂ))⁻¹ * ((Real.sqrt N : ℂ))⁻¹ = (N : ℂ)⁻¹ := by
    rw [← mul_inv]
    congr 1
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hNpos)]
  have hstar : ∀ j : Fin N, (star (qftMatrix N)) j l = (Real.sqrt N : ℂ)⁻¹ *
      zeta N ^ (-((l : ℕ) * (j : ℕ) : ℤ)) := by
    intro j
    have : (star (qftMatrix N)) j l = (starRingEnd ℂ) (qftMatrix N l j) := rfl
    rw [this, qftMatrix_apply]
    rw [map_mul, ← Complex.ofReal_inv, Complex.conj_ofReal, Complex.ofReal_inv]
    congr 1
    rw [map_pow]
    have hz : (starRingEnd ℂ) (zeta N) = (zeta N)⁻¹ := by
      unfold zeta
      rw [← Complex.exp_conj, ← Complex.exp_neg]
      congr 1
      simp [Complex.ext_iff]
    rw [hz, zpow_neg, ← inv_pow, zpow_natCast]
  simp only [Matrix.mul_apply, Matrix.one_apply]
  have key : ∀ j : Fin N, qftMatrix N k j * (star (qftMatrix N)) j l =
      (N : ℂ)⁻¹ * (zeta N ^ ((k : ℕ) - (l : ℕ) : ℤ)) ^ (j : ℕ) := by
    intro j
    rw [qftMatrix_apply, hstar j]
    rw [show (Real.sqrt N : ℂ)⁻¹ * zeta N ^ ((k : ℕ) * (j : ℕ)) *
        ((Real.sqrt N : ℂ)⁻¹ * zeta N ^ (-((l : ℕ) * (j : ℕ) : ℤ)))
        = ((Real.sqrt N : ℂ)⁻¹ * (Real.sqrt N : ℂ)⁻¹) *
          (zeta N ^ ((k : ℕ) * (j : ℕ)) * zeta N ^ (-((l : ℕ) * (j : ℕ) : ℤ))) by ring]
    rw [hsqrt]
    congr 1
    rw [← zpow_natCast (zeta N) ((k : ℕ) * (j : ℕ)), ← zpow_add₀ (zeta_ne_zero N),
      ← zpow_natCast (zeta N ^ (((k : ℕ) : ℤ) - ((l : ℕ) : ℤ))) (j : ℕ), ← zpow_mul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum]
  have habs : |(((k : ℕ) : ℤ) - ((l : ℕ) : ℤ))| < (N : ℤ) := by
    have hk : (k : ℕ) < N := k.isLt
    have hl : (l : ℕ) < N := l.isLt
    omega
  rw [sum_zeta_zpow N hN _ habs]
  by_cases hkl : k = l
  · subst hkl
    simp
    field_simp
  · rw [if_neg hkl, if_neg (by
      intro h
      exact hkl (Fin.ext (by omega))), mul_zero]

/-- **The 3-qubit QFT matrix is unitary.** -/
