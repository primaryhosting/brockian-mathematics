/-
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is a
-- plain block comment; it is repeated as the module docstring below.)

import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Finset Matrix SimpleGraph

namespace Chem

/-- The primitive 13-th root of unity `exp (2πi/13)`. -/

lemma adj_mulVec (v : Fin 13 → ℂ) (x : Fin 13) :
    ((cycleGraph 13).adjMatrix ℂ *ᵥ v) x = v (x - 1) + v (x + 1) := by
  have hne : x - 1 ≠ x + 1 := by
    simp only [sub_eq_add_neg, ne_eq, add_right_inj]
    decide
  rw [SimpleGraph.adjMatrix_mulVec_apply, cycleGraph_neighborFinset, Finset.sum_pair hne]

/-- **Hückel theory for the C₁₃ cycle.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₃` if and only if `μ = 2 cos (2πk/13)` for some
`k ∈ {0, …, 12}`. -/
