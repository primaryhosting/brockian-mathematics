import Mathlib
/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Polynomial

namespace Chem

/-- A primitive 8-th root of unity. -/

noncomputable def C8dft : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.vandermonde (fun j : Fin 8 => zeta8 ^ (j : ℕ))

