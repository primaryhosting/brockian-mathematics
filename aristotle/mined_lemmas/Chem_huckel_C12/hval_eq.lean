import Mathlib
/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix

/-- A primitive 12-th root of unity. -/

lemma hval_eq (k : Fin 12) : hval k = om ^ (k : ℕ) + (om ^ (k : ℕ))⁻¹ := by
  have h1 : om ^ (k : ℕ) = Complex.exp ((2 * Real.pi * (k : ℕ) / 12 : ℝ) * Complex.I) := by
    rw [om, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [hval, h1, ← Complex.exp_neg]
  push_cast
  rw [Complex.cos]
  ring_nf

