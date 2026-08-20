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

noncomputable def D : Matrix (Fin 18) (Fin 18) ℂ :=
  Matrix.diagonal (fun k : Fin 18 => (2 * Real.cos (2 * Real.pi * (k : ℕ) / 18) : ℂ))

