/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Polynomial

namespace Chem

/-- A primitive 11-th root of unity. -/

noncomputable def C11fourier : Matrix (Fin 11) (Fin 11) ℂ :=
  Matrix.vandermonde (fun k : Fin 11 => zeta11 ^ (k : ℕ))

