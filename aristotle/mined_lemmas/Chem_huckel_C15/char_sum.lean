/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
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

set_option grind.warning false

namespace Chem

open Finset SimpleGraph

/-- A primitive 15-th root of unity. -/

lemma char_sum (d : ℤ) :
    ∑ k : Fin 15, chi d k = if (15 : ℤ) ∣ d then 15 else 0 := by
  have hk : ∀ k : Fin 15, chi d k = (W d) ^ (k : ℕ) := by
    intro k
    simp [chi, W, zpow_mul, zpow_natCast]
  rw [Finset.sum_congr rfl (fun k _ => hk k), Fin.sum_univ_eq_sum_range (fun t => (W d) ^ t) 15]
  by_cases h : (15 : ℤ) ∣ d
  · have h1 : W d = 1 := (W_eq_one_iff d).mpr h
    simp [h1, h]
  · have hne : W d ≠ 1 := fun hc => h ((W_eq_one_iff d).mp hc)
    have h15 : (W d) ^ (15 : ℕ) = 1 := by
      have hEq : (W d) ^ (15 : ℕ) = W (d * 15) := by
        rw [W, W, ← zpow_natCast (zeta ^ d) 15, ← zpow_mul]
        norm_num
      rw [hEq, W_eq_one_iff]
      exact ⟨d, by ring⟩
    rw [geom_sum_eq hne, h15]
    simp [h]

