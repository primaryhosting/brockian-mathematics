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

lemma stdAddChar_add_neg (κ : ZMod 15) :
    (stdAddChar κ : ℂ) + (stdAddChar (-κ) : ℂ) = 2 * Real.cos (2 * Real.pi * κ.val / 15) := by
  set θ : ℝ := 2 * Real.pi * κ.val / 15 with hθ
  have h1 : (stdAddChar κ : ℂ) = Complex.exp (θ * I) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    congr 1
    push_cast [hθ]
    ring
  have h2 : (stdAddChar κ : ℂ) * (stdAddChar (-κ) : ℂ) = 1 := by
    rw [← AddChar.map_add_eq_mul]; simp
  have h3 : (stdAddChar (-κ) : ℂ) = Complex.exp (-(θ * I)) := by
    rw [Complex.exp_neg]
    refine (inv_eq_of_mul_eq_one_left ?_).symm
    rw [← h1, mul_comm]; exact h2
  rw [h1, h3, ← neg_mul, ← Complex.two_cos, Complex.ofReal_cos]

/-- The discrete Fourier transform diagonalises the adjacency matrix of `C₁₅`. -/
