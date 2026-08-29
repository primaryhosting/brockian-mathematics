import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Real Matrix Finset

namespace Chem

/-- A primitive 10-th root of unity. -/

def C10adj : Matrix (ZMod 10) (ZMod 10) ℂ :=
  Matrix.of fun i j => if i - j = 1 ∨ j - i = 1 then 1 else 0

/-- The Hückel eigenvalues `2 cos (2πk/10)`. -/
