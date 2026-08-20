/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Matrix Complex SimpleGraph Finset

namespace Chem

/-- The primitive 19-th root of unity `exp (2πi/19)`. -/

noncomputable def dftQ : Matrix (Fin 19) (Fin 19) ℂ :=
  fun k j => (19 : ℂ)⁻¹ * (zeta ^ (k.val * j.val))⁻¹

