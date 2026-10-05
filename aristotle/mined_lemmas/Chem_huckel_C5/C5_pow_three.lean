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

lemma C5_pow_three : C5 ^ 3 = C5 ^ 2 + (3 : ℝ) • C5 - (2 : ℝ) • (1 : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C5, pow_succ, Matrix.mul_apply, Fin.sum_univ_five] <;> norm_num

/-- `cos (2π/5) = (√5 - 1)/4`. -/
