/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix

namespace Chem

/-- A primitive fifth root of unity. -/

lemma e5_nat_mul (n : ℕ) (m : ZMod 5) : e5 ((n : ZMod 5) * m) = e5 m ^ n := by
  induction n with
  | zero => simp [e5_zero]
  | succ n ih =>
      have : ((n + 1 : ℕ) : ZMod 5) * m = (n : ZMod 5) * m + m := by push_cast; ring
      rw [this, e5_add, ih, pow_succ]

