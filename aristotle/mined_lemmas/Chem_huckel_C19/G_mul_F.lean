import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Matrix

namespace Chem

/-- A primitive 19-th root of unity. -/

lemma G_mul_F : G19 * F19 = 1 := mul_eq_one_comm.mp F_mul_G

/-- `F19` viewed as a unit of the matrix ring. -/
