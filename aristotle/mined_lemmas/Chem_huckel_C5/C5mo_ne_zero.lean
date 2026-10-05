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

lemma C5mo_ne_zero (k : ℕ) : C5mo k ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [C5mo] at h0

/-- The `k`-th Hückel orbital is an eigenvector of the `C₅` adjacency matrix with
eigenvalue `2 cos (2πk/5)`. -/
