/-
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open Complex Polynomial SimpleGraph

namespace Chem

/-- A primitive `9`-th root of unity. -/

theorem ff_add_ff_neg (k : ZMod 9) :
    ff k + ff (-k) = ((2 * Real.cos (2 * Real.pi * k.val / 9) : ℝ) : ℂ) := by
  rw [ff_neg, ff_exp, ← Complex.exp_neg, ← neg_mul, ← Complex.ofReal_neg]
  simp only [Complex.exp_mul_I, Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

/-- Entrywise description of the adjacency matrix of `C₉`. -/
