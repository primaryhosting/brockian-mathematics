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

lemma ch_eq_exp (k : ZMod 16) :
    ch k = Complex.exp ((2 * Real.pi * (k.val : ℝ) / 16 : ℝ) * Complex.I) := by
  rw [ch, zeta16, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The eigenvalue attached to the character indexed by `k`. -/
