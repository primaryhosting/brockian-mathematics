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

lemma ee_natCast_mul (n : ℕ) (x : ZMod 16) : ee ((n : ZMod 16) * x) = ee x ^ n := by
  induction n with
  | zero => simp [ee_zero]
  | succ n ih =>
      have : ((n + 1 : ℕ) : ZMod 16) * x = (n : ZMod 16) * x + x := by push_cast; ring
      rw [this, ee_add, ih, pow_succ]

