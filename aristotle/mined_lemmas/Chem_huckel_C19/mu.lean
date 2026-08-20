/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open Complex (I)
open Matrix

namespace Chem

/-- The primitive 19-th root of unity `exp (2πi/19)`. -/

noncomputable def mu (k : Fin 19) : ℂ := 2 * Real.cos (2 * Real.pi * (k : ℕ) / 19)

/-- The adjacency matrix of the cycle graph `C₁₉` over `ℂ`. -/
