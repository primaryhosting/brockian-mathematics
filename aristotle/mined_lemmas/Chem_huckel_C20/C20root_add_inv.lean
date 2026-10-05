/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Complex Matrix Polynomial

namespace Chem

/-- The adjacency matrix of the cycle graph `C₂₀`, with vertices indexed by `ZMod 20`:
vertex `i` is adjacent exactly to `i + 1` and `i - 1`.  In Hückel theory (with `α = 0`,
`β = 1`) this is the Hückel matrix of the annulene `C₂₀`. -/

lemma C20root_add_inv (k : ZMod 20) :
    C20root k + (C20root k)⁻¹ = ((C20eigenvalue k : ℝ) : ℂ) := by
  rw [C20eigenvalue, C20root]
  push_cast
  rw [Complex.two_cos, ← Complex.exp_neg]
  ring_nf

/-- Each `2 cos (2πk/20)` is an eigenvalue of the adjacency matrix of `C₂₀`,
with explicit eigenvector `C20vec k`. -/
