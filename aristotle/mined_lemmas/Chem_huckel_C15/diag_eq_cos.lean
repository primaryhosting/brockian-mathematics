import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset SimpleGraph

/-- A primitive 15-th root of unity. -/

lemma diag_eq_cos (l : Fin 15) :
    g l + (g l)⁻¹ = ((2 * Real.cos (2 * Real.pi * l.val / 15) : ℝ) : ℂ) := by
  have h1 : g l = Complex.exp ((2 * Real.pi * l.val / 15 : ℝ) * Complex.I) := by
    rw [g, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h1, ← Complex.exp_neg]
  push_cast
  rw [Complex.two_cos, neg_mul]

/-- **Hückel theory for the cycle `C₁₅`.**  The eigenvalues (spectrum) of the adjacency matrix
of the cycle graph on 15 vertices are exactly the numbers `2 * cos (2 * π * k / 15)`,
`k = 0, 1, …, 14`. -/
