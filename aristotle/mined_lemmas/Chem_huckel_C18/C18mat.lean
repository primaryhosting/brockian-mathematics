/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Polynomial Finset

noncomputable section

/-- A primitive 18-th root of unity. -/

def C18mat : Matrix (ZMod 18) (ZMod 18) ℂ :=
  Matrix.circulant (fun i => if i = 1 ∨ i = -1 then 1 else 0)

/-- The `k`-th Hückel eigenvalue `2 cos (2πk/18)`. -/
