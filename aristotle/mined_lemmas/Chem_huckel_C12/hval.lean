import Mathlib
/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix

/-- A primitive 12-th root of unity. -/

noncomputable def hval (k : Fin 12) : ℂ := ((2 * Real.cos (2 * Real.pi * k / 12) : ℝ) : ℂ)

/-- The DFT (Vandermonde) matrix, whose `k`-th column is the eigenvector belonging to
the eigenvalue `hval k`. -/
