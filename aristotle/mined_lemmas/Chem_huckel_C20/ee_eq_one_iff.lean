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

set_option maxHeartbeats 1000000

namespace Chem

open Complex Matrix Polynomial Finset

/-- A primitive 20-th root of unity. -/

lemma ee_eq_one_iff (m : Fin 20) : ee m = 1 ↔ m = 0 := by
  constructor
  · intro h
    by_contra hm
    have h0 : (m : ℕ) ≠ 0 := by
      intro hh
      exact hm (Fin.val_eq_zero_iff.mp hh)
    exact zeta_primitive.pow_ne_one_of_pos_of_lt h0 m.isLt h
  · rintro rfl; exact ee_zero

