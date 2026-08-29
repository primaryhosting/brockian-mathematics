import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The primitive 15-th root of unity `exp(2πi/15)`. -/

lemma v_ne_zero (k : ZMod 15) : v k ≠ 0 := by
  intro h
  have : v k 0 = 0 := by rw [h]; rfl
  rw [v, mul_zero, chi_zero] at this
  exact one_ne_zero this

/-- **Hückel theory for the cycle `C₁₅`.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₅` if and only if `μ = 2·cos(2πk/15)` for some
`k ∈ {0, 1, …, 14}`. -/
