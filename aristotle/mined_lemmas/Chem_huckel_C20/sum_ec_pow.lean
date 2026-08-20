/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
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

open Polynomial Matrix

/-! ### The 20-th root of unity and the characters of `Fin 20` -/

/-- The primitive 20-th root of unity `exp (2πi/20)`. -/

lemma sum_ec_pow (d : Fin 20) :
    (∑ m : Fin 20, ec (m * d)) = if d = 0 then (20 : ℂ) else 0 := by
  have hrw : (∑ m : Fin 20, ec (m * d)) = ∑ i ∈ Finset.range 20, (ec d) ^ i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => (ec d) ^ i) 20]
    exact Finset.sum_congr rfl fun m _ => ec_mul_pow m d
  rw [hrw]
  by_cases hd : d = 0
  · subst hd
    simp [ec_zero]
  · rw [if_neg hd, geom_sum_eq (ec_ne_one hd)]
    have h20 : (ec d) ^ (20 : ℕ) = 1 := by
      rw [ec, ← pow_mul, mul_comm, pow_mul, zeta20_pow_20, one_pow]
    rw [h20, sub_self, zero_div]

