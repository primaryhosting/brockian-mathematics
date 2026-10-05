import Mathlib
/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix

/-- A primitive 12-th root of unity. -/

def C12 : Matrix (Fin 12) (Fin 12) ℂ :=
  fun i j => if (i.val + 1) % 12 = j.val ∨ (j.val + 1) % 12 = i.val then 1 else 0

/-- The Hückel eigenvalues `2 cos (2πk/12)`. -/
