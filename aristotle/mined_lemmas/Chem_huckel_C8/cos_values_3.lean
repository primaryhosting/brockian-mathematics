/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Real Matrix SimpleGraph

namespace Chem

/-- The adjacency matrix (over `ℝ`) of the cycle graph `C₈`, i.e. the Hückel matrix of
cyclooctatetraene in units where `α = 0` and `β = 1`. -/

lemma cos_values_3 : 2 * Real.cos (2 * π * (3 : ℕ) / 8) = -Real.sqrt 2 := by
  rw [show 2 * π * ((3 : ℕ) : ℝ) / 8 = π - π / 4 by push_cast; ring, Real.cos_pi_sub,
    Real.cos_pi_div_four]
  ring

/-- **Hückel theory for cyclooctatetraene (C₈).**
A real number `μ` is an eigenvalue of the adjacency matrix of the cycle graph `C₈`
if and only if `μ = 2 cos (2πk/8)` for some `k ∈ {0, …, 7}`. -/
