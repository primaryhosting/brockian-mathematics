/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Complex Polynomial Matrix SimpleGraph

namespace Chem

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/

noncomputable def F18 : Matrix (Fin 18) (Fin 18) ℂ :=
  Matrix.vandermonde (fun j => zeta18 ^ (j : ℕ))

