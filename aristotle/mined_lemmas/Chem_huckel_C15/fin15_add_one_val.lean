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

lemma fin15_add_one_val (i : Fin 15) : ((i + 1 : Fin 15) : ℕ) = ((i : ℕ) + 1) % 15 := by
  simp [Fin.add_def]

