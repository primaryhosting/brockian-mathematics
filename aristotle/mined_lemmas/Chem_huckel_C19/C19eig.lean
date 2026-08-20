/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators Real

namespace Chem

open Complex Matrix Finset

/-- A primitive 19-th root of unity. -/

noncomputable def C19eig (k : ZMod 19) : ℂ := 2 * (Real.cos (2 * Real.pi * k.val / 19) : ℝ)

/-- The discrete Fourier matrix, whose columns are the eigenvectors of `C19adj`. -/
