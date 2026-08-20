/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators Real

namespace Chem

open Complex Matrix Finset

/-- A primitive 19-th root of unity. -/

def C19adj : Matrix (ZMod 19) (ZMod 19) ℂ :=
  fun i j => (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0)

/-- The Hückel eigenvalues `2 cos (2πk/19)`. -/
