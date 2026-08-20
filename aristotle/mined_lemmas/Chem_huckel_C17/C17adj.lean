/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Complex

/-! ### A primitive 17-th root of unity and the associated additive character -/

/-- A primitive 17-th root of unity. -/

def C17adj : Matrix (ZMod 17) (ZMod 17) ℂ :=
  Matrix.of fun i j => if i - j = 1 ∨ j - i = 1 then 1 else 0

/-- The adjacency matrix is symmetric. -/
