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

noncomputable def ee (a : Fin 19) : ℂ := om ^ (a : ℕ)

/-- The Hückel eigenvalues of the cycle `C₁₉`. -/
