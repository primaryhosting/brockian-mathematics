/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 does not
-- permit a module docstring before the `import` line.)

import Mathlib

namespace Chem

open Finset Complex Matrix

/-- A primitive 16-th root of unity. -/

lemma ch_mul (k m : ZMod 16) : ch (k * m) = ch m ^ k.val := by
  rw [← ch_nsmul]
  congr 1
  rw [nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id]

