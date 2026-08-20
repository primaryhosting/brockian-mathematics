import Mathlib
/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Complex Matrix

namespace Chem

/-- A primitive 13-th root of unity. -/

lemma e13_eq_exp (k : ZMod 13) :
    e13 k = Complex.exp ((2 * Real.pi * (k.val : ℝ) / 13 : ℝ) * Complex.I) := by
  rw [e13, omega13, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

