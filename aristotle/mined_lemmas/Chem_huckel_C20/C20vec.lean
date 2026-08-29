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

noncomputable def C20vec (k : ZMod 20) : ZMod 20 → ℂ :=
  fun i => Complex.exp (((2 * Real.pi * (k.val : ℝ) / 20 : ℝ) : ℂ) * Complex.I) ^ i.val

/-- Multiplying the adjacency matrix into a vector adds the two neighbouring entries. -/
