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

noncomputable def C20eigenvalue (k : ZMod 20) : ℝ :=
  2 * Real.cos (2 * Real.pi * (k.val : ℝ) / 20)

/-- The `k`-th (unnormalized) Hückel eigenvector of `C₂₀`:
its `i`-th entry is `exp (2πi·k/20) ^ i`. -/
