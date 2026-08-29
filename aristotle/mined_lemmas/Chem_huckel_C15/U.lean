/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat

set_option maxHeartbeats 1000000

namespace Chem

open SimpleGraph Matrix

/-- A primitive 15-th root of unity. -/

noncomputable def U : Matrix (Fin 15) (Fin 15) ℂ :=
  Matrix.vandermonde (fun i : Fin 15 => zeta ^ (i : ℕ))

