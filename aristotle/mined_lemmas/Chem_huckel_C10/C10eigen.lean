import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Real Matrix Finset

namespace Chem

/-- A primitive 10-th root of unity. -/

noncomputable def C10eigen (k : ZMod 10) : ℂ := 2 * (Real.cos (2 * Real.pi * k.val / 10) : ℝ)

/-- The (unnormalized) discrete Fourier matrix, whose `k`-th column is the eigenvector
`j ↦ ω^{jk}`. -/
