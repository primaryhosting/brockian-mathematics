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

lemma ch_nsmul (n : ℕ) (x : ZMod 16) : ch (n • x) = ch x ^ n := by
  induction n with
  | zero => simpa using ch_zero
  | succ n ih => rw [succ_nsmul, ch_add, ih, pow_succ]

