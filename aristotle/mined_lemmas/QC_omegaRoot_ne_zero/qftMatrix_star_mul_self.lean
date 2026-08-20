/-
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/

lemma qftMatrix_star_mul_self {n : ℕ} (hn : n ≠ 0) :
    star (qftMatrix n) * qftMatrix n = 1 := by
  have hω0 : omegaRoot n ≠ 0 := omegaRoot_ne_zero n
  have hsqrt : ((Real.sqrt n : ℂ))⁻¹ * ((Real.sqrt n : ℂ))⁻¹ * (n : ℂ) = 1 := by
    have h1 : ((Real.sqrt n : ℂ)) * ((Real.sqrt n : ℂ)) = (n : ℂ) := by
      have := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) n)
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) this
    have h2 : ((Real.sqrt n : ℂ)) ≠ 0 := by
      have : Real.sqrt n ≠ 0 := by
        have : (0:ℝ) < n := by positivity
        positivity
      exact_mod_cast this
    field_simp [← h1]
    rw [sq, h1]
  ext i k
  rw [Matrix.mul_apply, Matrix.one_apply]
  have key : ∀ j : Fin n, star (qftMatrix n) i j * qftMatrix n j k
      = ((Real.sqrt n : ℂ))⁻¹ * ((Real.sqrt n : ℂ))⁻¹
        * (omegaRoot n ^ ((k : ℤ) - (i : ℤ))) ^ (j : ℕ) := by
    intro j
    rw [Matrix.star_apply, qftMatrix_apply, qftMatrix_apply, star_mul', star_pow, star_omegaRoot]
    have hinv : ((omegaRoot n)⁻¹) ^ ((j : ℕ) * (i : ℕ)) * omegaRoot n ^ ((j : ℕ) * (k : ℕ))
        = (omegaRoot n ^ ((k : ℤ) - (i : ℤ))) ^ (j : ℕ) := by
      rw [← zpow_natCast ((omegaRoot n)⁻¹) ((j : ℕ) * (i : ℕ)),
        ← zpow_natCast (omegaRoot n) ((j : ℕ) * (k : ℕ)),
        ← zpow_natCast (omegaRoot n ^ ((k : ℤ) - (i : ℤ))) (j : ℕ),
        ← zpow_mul, inv_zpow', ← zpow_add₀ hω0]
      congr 1
      push_cast
      ring
    have hstarR : star ((Real.sqrt n : ℂ))⁻¹ = ((Real.sqrt n : ℂ))⁻¹ := by
      simp [← Complex.ofReal_inv]
    rw [hstarR, mul_mul_mul_comm, hinv]
  rw [Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j => (omegaRoot n ^ ((k : ℤ) - (i : ℤ))) ^ j) n]
  by_cases hik : i = k
  · subst hik
    simp only [sub_self, zpow_zero, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one]
    exact hsqrt
  · rw [if_neg hik]
    have hd : ¬ ((n : ℤ) ∣ ((k : ℤ) - (i : ℤ))) := by
      intro h
      have habs : |((k : ℤ) - (i : ℤ))| < (n : ℤ) := by
        have hi := i.isLt
        have hk := k.isLt
        have : (i : ℤ) < n := by exact_mod_cast hi
        have : (k : ℤ) < n := by exact_mod_cast hk
        rw [abs_lt]
        constructor <;> omega
      have := Int.eq_zero_of_abs_lt_dvd h habs
      apply hik
      have : (i : ℕ) = (k : ℕ) := by omega
      exact Fin.ext this
    rw [geom_sum_omegaRoot hn _ hd, mul_zero]

/-- The `n`-dimensional QFT matrix is unitary, for any `n > 0`. -/
