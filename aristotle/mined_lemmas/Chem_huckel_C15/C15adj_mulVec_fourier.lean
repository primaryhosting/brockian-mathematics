/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hückel theory for the cycle `C₁₅`

The eigenvalues of the adjacency matrix of the cycle graph `C₁₅` are exactly the
numbers `2 cos (2πk/15)` for `k = 0, …, 14`.  (In Hückel molecular orbital theory these
are the orbital energies `α + 2β cos(2πk/15)` of a cyclic conjugated system with 15
centres, in units where `α = 0`, `β = 1`.)

The proof diagonalises the (circulant) adjacency matrix using the discrete Fourier
transform on `ZMod 15`.
-/

namespace Chem

open Complex Finset ZMod

/-- The adjacency matrix of the cycle graph `C₁₅`, with vertices indexed by `ZMod 15`:
two vertices are adjacent exactly when they differ by `1`. -/

lemma C15adj_mulVec_fourier (κ : ZMod 15) :
    C15adj.mulVec (fun j => (stdAddChar (j * κ) : ℂ))
      = ((stdAddChar κ : ℂ) + (stdAddChar (-κ) : ℂ)) • (fun j => (stdAddChar (j * κ) : ℂ)) := by
  funext i
  rw [C15adj_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul]
  have h1 : ((i - 1) * κ) = (-κ) + i * κ := by ring
  have h2 : ((i + 1) * κ) = κ + i * κ := by ring
  rw [h1, h2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  ring

/-- **Hückel theory for the cycle `C₁₅`.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₅` if and only if `μ = 2 cos (2πk/15)` for some
`k ∈ {0, …, 14}`. -/
