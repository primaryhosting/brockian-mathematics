/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix SimpleGraph Complex

/-- The primitive 18-th root of unity `exp(2πi/18)`. -/

noncomputable def V : Matrix (Fin 18) (Fin 18) ℂ :=
  Matrix.vandermonde (fun j : Fin 18 => om ^ (j : ℕ))

