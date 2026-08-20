import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Polynomial

namespace Chem

/-- A primitive 9th root of unity. -/

theorem Vm_mul_Wm : Vm * Wm = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin 9, Vm j k * Wm k l
      = (9 : ℂ)⁻¹ * (om ^ ((j : ℕ) + (9 - (l : ℕ)))) ^ (k : ℕ) := by
    intro k
    have hpow : om ^ ((j : ℕ) * (k : ℕ)) * om ^ ((k : ℕ) * (9 - (l : ℕ)))
        = (om ^ ((j : ℕ) + (9 - (l : ℕ)))) ^ (k : ℕ) := by
      rw [← pow_add, ← pow_mul]
      congr 1
      ring
    simp only [Vm, Wm]
    rw [← hpow]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum, sum_om_pow]
  have hl : (l : ℕ) < 9 := l.isLt
  have hj : (j : ℕ) < 9 := j.isLt
  by_cases hjl : j = l
  · subst hjl
    have h0 : ((j : ℕ) + (9 - (j : ℕ))) % 9 = 0 := by omega
    rw [if_pos h0]
    simp
  · have hne : (j : ℕ) ≠ (l : ℕ) := fun h => hjl (Fin.ext h)
    have h0 : ((j : ℕ) + (9 - (l : ℕ))) % 9 ≠ 0 := by omega
    rw [if_neg h0]
    simp [hjl]

