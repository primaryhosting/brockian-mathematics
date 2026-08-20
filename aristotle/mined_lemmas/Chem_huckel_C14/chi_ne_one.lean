import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset Complex

set_option maxHeartbeats 1000000

namespace Chem

/-- A primitive 14-th root of unity. -/

lemma chi_ne_one {m : Fin 14} (hm : m ≠ 0) : chi m ≠ 1 := by
  have h0 : m.val ≠ 0 := by
    intro h
    exact hm (by ext; simpa using h)
  exact om_primitive.pow_ne_one_of_pos_of_lt h0 m.isLt

