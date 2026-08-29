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

lemma V12_apply (i k : Fin 12) : V12 i k = (om ^ (k : ℕ)) ^ (i : ℕ) := by
  simp [V12, Matrix.vandermonde, ← pow_mul, Nat.mul_comm]

/-- The row-`i` recursion for the cycle: `u^{i-1} + u^{i+1} = u^i (u + u^{-1})`, written with
`u^11` in place of `u⁻¹` using `u^12 = 1`. -/
