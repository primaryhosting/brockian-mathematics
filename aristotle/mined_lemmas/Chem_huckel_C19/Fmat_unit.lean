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

theorem Fmat_unit :
    ∃ u : (Matrix (Fin 19) (Fin 19) ℂ)ˣ, (u : Matrix (Fin 19) (Fin 19) ℂ) = Fmat :=
  ⟨⟨Fmat, Gmat, Fmat_mul_Gmat, mul_eq_one_comm.mp Fmat_mul_Gmat⟩, rfl⟩

