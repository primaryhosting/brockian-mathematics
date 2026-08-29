/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Real Matrix

/-- Adjacency matrix of the cycle graph `C₃` (the Hückel matrix of cyclopropenyl,
in units where `α = 0` and `β = 1`). -/

lemma C3eigenvalue_zero : C3eigenvalue 0 = 2 := by
  simp [C3eigenvalue]

