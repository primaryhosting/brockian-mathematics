import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
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

namespace Chem

open scoped Matrix

/-! ### A primitive 14-th root of unity and the associated character -/

/-- A primitive 14-th root of unity. -/

theorem sum_ee (d : ℤ) (hd : ¬ (14 : ℤ) ∣ d) :
    ∑ k : Fin 14, ee (((k : ℕ) : ℤ) * d) = 0 := by
  have hz : ee d ≠ 1 := fun h => hd (ee_eq_one_iff.mp h)
  have hterm : ∀ k : Fin 14, ee (((k : ℕ) : ℤ) * d) = (ee d) ^ ((k : ℕ)) := by
    intro k
    rw [ee_intCast_mul, zpow_natCast]
  simp only [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun i => (ee d) ^ i) 14, geom_sum_eq hz]
  have h14 : (ee d) ^ (14 : ℕ) = 1 := by
    rw [ee, ← zpow_natCast (om ^ d) 14, ← zpow_mul, mul_comm, zpow_mul,
      show ((14 : ℕ) : ℤ) = (14 : ℤ) from by norm_num, om_zpow_14, one_zpow]
  rw [h14, sub_self, zero_div]

