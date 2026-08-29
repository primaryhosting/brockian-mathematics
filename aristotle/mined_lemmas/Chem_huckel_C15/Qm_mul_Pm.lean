import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset SimpleGraph

/-- A primitive 15-th root of unity. -/

lemma Qm_mul_Pm : Qm * Pm = 1 := mul_eq_one_comm.mp Pm_mul_Qm

