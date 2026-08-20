import Mathlib
/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix

/-- The adjacency matrix of the cycle graph `C₁₈`, with vertices indexed by `ZMod 18`:
two vertices are adjacent iff they differ by `1` modulo `18`. -/

theorem C18adj_mulVec_eq (k : ZMod 18) :
    C18adj *ᵥ (fun j => w (j * k))
        = ((2 * Real.cos (2 * Real.pi * k.val / 18) : ℝ) : ℂ) • (fun j => w (j * k))
      ∧ (fun j : ZMod 18 => w (j * k)) ≠ 0 := by
  constructor
  · funext j
    have h := congrFun (congrFun C18adj_mul_Fmat j) k
    rw [Dmat, Matrix.mul_diagonal] at h
    simp only [Matrix.mul_apply, Fmat, Matrix.of_apply] at h
    simpa [Matrix.mulVec, dotProduct, mul_comm] using h
  · intro h
    have h0 := congrFun h 0
    simp [w] at h0

/-- The adjacency eigenvalues of the cycle graph `C₁₈` are exactly the numbers
`2 cos (2πk/18)`, `k = 0, …, 17`. -/
