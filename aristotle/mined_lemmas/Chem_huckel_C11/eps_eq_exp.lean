/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Finset

/-- A primitive 11-th root of unity. -/

lemma eps_eq_exp (x : ZMod 11) :
    eps x = Complex.exp ((2 * Real.pi * (x.val : ℝ) / 11 : ℝ) * Complex.I) := by
  rw [eps, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

