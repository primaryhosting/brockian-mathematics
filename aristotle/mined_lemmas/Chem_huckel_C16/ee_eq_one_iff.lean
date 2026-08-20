import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header block is placed immediately after `import Mathlib`, since Lean 4 requires
-- `import` commands to come first in a file.)

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Finset

/-- A primitive 16-th root of unity. -/

lemma ee_eq_one_iff (x : ZMod 16) : ee x = 1 ↔ x = 0 := by
  constructor
  · intro h
    have hdvd : (16 : ℕ) ∣ x.val := (zeta_primitive.pow_eq_one_iff_dvd x.val).1 h
    have hlt : x.val < 16 := ZMod.val_lt x
    exact (ZMod.val_eq_zero x).1 (Nat.eq_zero_of_dvd_of_lt hdvd hlt)
  · rintro rfl; exact ee_zero

