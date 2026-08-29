/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex

/-- The adjacency matrix of the cycle graph `C₇`, indexed by `ZMod 7`:
vertices `i` and `j` are adjacent iff they differ by `1` modulo `7`. -/

theorem zeta_pow_seven : zeta ^ 7 = 1 := by
  rw [zeta, ← Complex.exp_nat_mul,
    show (7 : ℕ) * (2 * (Real.pi : ℂ) * Complex.I / 7) = 2 * Real.pi * Complex.I by
      push_cast; ring]
  exact Complex.exp_two_pi_mul_I

