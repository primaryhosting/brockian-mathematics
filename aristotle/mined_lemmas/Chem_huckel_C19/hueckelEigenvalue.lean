import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Matrix

namespace Chem

/-- A primitive 19-th root of unity. -/

noncomputable def hueckelEigenvalue (k : Fin 19) : ℂ :=
  ((2 * Real.cos (2 * Real.pi * k.val / 19) : ℝ) : ℂ)

/-- The diagonal matrix of Hückel eigenvalues. -/
