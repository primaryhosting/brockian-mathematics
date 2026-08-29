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

lemma ch_add (x y : ZMod 16) : ch (x + y) = ch x * ch y := by
  simp only [ch, ZMod.val_add, zeta16_pow_mod, pow_add]

