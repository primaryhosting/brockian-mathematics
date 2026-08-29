/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace Chem

open Matrix

/-- The adjacency matrix of the cycle graph `C₅` (the Hückel matrix of cyclopentadienyl
in units where the Coulomb integral `α` is `0` and the resonance integral `β` is `1`). -/

lemma C5_mulVec_ones : C5 *ᵥ ![1, 1, 1, 1, 1] = (2 : ℝ) • ![1, 1, 1, 1, 1] := by
  ext i
  fin_cases i <;> simp [C5, Matrix.mulVec, dotProduct, Fin.sum_univ_five] <;> norm_num

/-- For a root `μ` of `x² + x - 1`, the vector `(2, μ, -1-μ, -1-μ, μ)` is an eigenvector of `C5`
for the eigenvalue `μ`. -/
