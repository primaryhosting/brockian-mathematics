/-
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open Complex Polynomial SimpleGraph

namespace Chem

/-- A primitive `9`-th root of unity. -/

theorem fourier9_eq_vandermonde :
    fourier9 = Matrix.vandermonde (fun k : Fin 9 => zeta ^ (k : ℕ)) := by
  ext j k
  simp only [fourier9, Matrix.of_apply, Matrix.vandermonde_apply, ff, ← pow_mul]
  exact zeta_pow_mod _

