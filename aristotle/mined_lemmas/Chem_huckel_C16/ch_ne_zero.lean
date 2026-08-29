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

lemma ch_ne_zero (x : ZMod 16) : ch x ≠ 0 := by
  simp only [ch]
  exact pow_ne_zero _ (by simp [zeta16, Complex.exp_ne_zero])

