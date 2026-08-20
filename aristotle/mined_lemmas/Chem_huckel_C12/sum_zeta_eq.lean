/-
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
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

namespace Chem

open Finset Matrix

/-- `zeta a = exp (2πi a / 12)`, the `a`-th power of a primitive 12th root of unity. -/

lemma sum_zeta_eq (d : ℤ) :
    ∑ k : Fin 12, zeta ((k.val : ℤ) * d) = if d % 12 = 0 then 12 else 0 := by
  have hq : ∀ k : Fin 12, zeta ((k.val : ℤ) * d) = zeta d ^ k.val := by
    intro k
    rw [zeta_eq_zpow ((k.val : ℤ) * d), zeta_eq_zpow d, ← zpow_natCast (zeta 1 ^ d) k.val,
      ← _root_.zpow_mul]
    congr 1
    ring
  simp only [hq]
  rw [Fin.sum_univ_eq_sum_range (fun k => zeta d ^ k) 12]
  by_cases h : d % 12 = 0
  · rw [if_pos h, zeta_eq_one_iff.mpr h]
    simp
  · rw [if_neg h]
    have h1 : zeta d ≠ 1 := fun hc => h (zeta_eq_one_iff.mp hc)
    rw [geom_sum_eq h1]
    have h12 : zeta d ^ (12 : ℕ) = 1 := by
      rw [zeta_eq_zpow d, ← zpow_natCast (zeta 1 ^ d) 12, ← _root_.zpow_mul,
        show (d * ((12 : ℕ) : ℤ)) = 12 * d by push_cast; ring, _root_.zpow_mul,
        zeta_one_pow_twelve, _root_.one_zpow]
    rw [h12]
    simp

