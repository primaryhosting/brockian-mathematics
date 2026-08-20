/-
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Real Matrix

/-- Adjacency matrix of the cycle graph `C₃` (the Hückel matrix of cyclopropenyl,
with `α = 0`, `β = 1`). -/

lemma two_cos_values (k : Fin 3) :
    2 * Real.cos (2 * π * (k : ℕ) / 3) = if k = 0 then 2 else -1 := by
  fin_cases k
  · norm_num
  · rw [show (2 * π * ((1 : ℕ) : ℝ) / 3) = π - π / 3 by push_cast; ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
  · rw [show (2 * π * ((2 : ℕ) : ℝ) / 3) = π + π / 3 by push_cast; ring, Real.cos_add]
    simp [Real.cos_pi_div_three]

/-- **Hückel theory for `C₃`.**  A real number `μ` is an eigenvalue of the adjacency
matrix of the cycle graph `C₃` (i.e. there is a nonzero vector `v` with `A v = μ v`)
if and only if `μ = 2 cos (2πk/3)` for some `k ∈ {0, 1, 2}`. -/
