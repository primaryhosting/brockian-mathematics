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

lemma eps_add_eps_neg (x : ZMod 11) :
    eps x + eps (-x) = ((2 * Real.cos (2 * Real.pi * (x.val : ℝ) / 11) : ℝ) : ℂ) := by
  have h1 : eps (-x) = Complex.exp (-((2 * Real.pi * (x.val : ℝ) / 11 : ℝ) * Complex.I)) := by
    rw [eps_neg, eps_eq_exp, ← Complex.exp_neg]
  rw [eps_eq_exp x, h1]
  push_cast
  rw [Complex.two_cos, neg_mul]

/-- The action of the adjacency matrix. -/
