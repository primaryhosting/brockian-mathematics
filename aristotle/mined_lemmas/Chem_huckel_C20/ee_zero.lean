import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Matrix Polynomial Finset

/-- A primitive 20-th root of unity. -/

lemma ee_zero : ee 0 = 1 := by simp [ee]

