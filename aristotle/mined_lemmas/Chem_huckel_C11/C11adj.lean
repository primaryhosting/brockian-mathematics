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

def C11adj : Matrix (Fin 11) (Fin 11) ℂ :=
  fun i j => if j = i + 1 ∨ i = j + 1 then 1 else 0

/-- The Hückel eigenvalues of `C₁₁` : `2 cos (2πk/11)`, `k = 0, …, 10`. -/
