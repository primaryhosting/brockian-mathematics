/-
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real

namespace QC

open Complex Matrix Finset

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/

lemma qft_row_orthogonality (n : ℕ) (hn : n ≠ 0) (k l : Fin n) :
    ∑ j : Fin n, zeta n ^ ((k : ℕ) * (j : ℕ)) * (zeta n ^ ((l : ℕ) * (j : ℕ)))⁻¹
      = if k = l then (n : ℂ) else 0 := by
  have hz : IsPrimitiveRoot (zeta n) n := zeta_isPrimitiveRoot n hn
  have hzne : zeta n ≠ 0 := by
    intro h
    have := abs_zeta n
    rw [h] at this
    simp at this
  set x : ℂ := zeta n ^ ((k : ℤ) - (l : ℤ)) with hxdef
  have hterm : ∀ j : Fin n,
      zeta n ^ ((k : ℕ) * (j : ℕ)) * (zeta n ^ ((l : ℕ) * (j : ℕ)))⁻¹ = x ^ (j : ℕ) := by
    intro j
    rw [hxdef, ← zpow_natCast (zeta n) ((k : ℕ) * (j : ℕ)),
      ← zpow_natCast (zeta n) ((l : ℕ) * (j : ℕ)), ← _root_.zpow_neg, ← zpow_add₀ hzne,
      ← zpow_natCast (zeta n ^ ((k : ℤ) - (l : ℤ))) (j : ℕ), ← _root_.zpow_mul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  by_cases hkl : k = l
  · subst hkl
    simp [hxdef]
  · rw [if_neg hkl]
    apply sum_pow_eq_zero
    · rw [hxdef, ← zpow_natCast (zeta n ^ ((k : ℤ) - (l : ℤ))) n, ← _root_.zpow_mul, mul_comm,
        _root_.zpow_mul, hz.zpow_eq_one, _root_.one_zpow]
    · rw [hxdef]
      intro h
      rw [hz.zpow_eq_one_iff_dvd] at h
      have hk : (k : ℕ) < n := k.isLt
      have hl : (l : ℕ) < n := l.isLt
      have habs : |((k : ℤ) - (l : ℤ))| < (n : ℤ) := by
        rw [abs_lt]
        omega
      have hzero : ((k : ℤ) - (l : ℤ)) = 0 := Int.eq_zero_of_abs_lt_dvd h habs
      have hkln : (k : ℕ) = (l : ℕ) := by omega
      exact hkl (Fin.ext hkln)

/-- The `n × n` QFT matrix is unitary. -/
