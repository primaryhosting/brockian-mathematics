import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 4000000
set_option maxRecDepth 40000

namespace Chem

open Matrix

/-- The adjacency matrix of the cycle graph `C₅` on vertices `0,1,2,3,4`:
vertices `i` and `j` are adjacent iff `j ≡ i + 1` or `i ≡ j + 1` modulo `5`. -/

lemma C5mo_apply (k : ℕ) (j : Fin 5) :
    C5mo k j = (Complex.exp (((2 * π * k / 5 : ℝ) : ℂ) * Complex.I)) ^ (j : ℕ) := by
  rw [C5mo, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

