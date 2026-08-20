/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators Real

namespace Chem

open Complex Matrix Finset

/-- A primitive 19-th root of unity. -/

lemma om_pow_eq_exp (m : ℕ) :
    om ^ m = Complex.exp (((2 * Real.pi * m / 19 : ℝ) : ℂ) * Complex.I) := by
  rw [om, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

