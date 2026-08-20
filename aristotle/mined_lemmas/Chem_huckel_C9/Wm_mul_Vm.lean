import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Polynomial

namespace Chem

/-- A primitive 9th root of unity. -/

theorem Wm_mul_Vm : Wm * Vm = 1 := mul_eq_one_comm.1 Vm_mul_Wm

/-- The eigenvalue attached to index `k` : `2 cos (2πk/9)`. -/
