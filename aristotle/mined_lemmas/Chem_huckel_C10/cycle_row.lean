/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Chem

open Polynomial Matrix Complex

/-- A primitive 10-th root of unity. -/

lemma cycle_row (z : ℂ) (h10 : z ^ (10 : ℕ) = 1) (i : Fin 10) :
    ∑ j : Fin 10, (if (SimpleGraph.cycleGraph 10).Adj i j then (1 : ℂ) else 0) * z ^ (j : ℕ)
      = z ^ (i : ℕ) * (z + z ^ 9) := by
  fin_cases i <;> simp +decide [Fin.sum_univ_succ]
  all_goals
    first
      | ring1
      | linear_combination (-1 : ℂ) * h10
      | linear_combination (-z) * h10
      | linear_combination (-z ^ 2) * h10
      | linear_combination (-z ^ 3) * h10
      | linear_combination (-z ^ 4) * h10
      | linear_combination (-z ^ 5) * h10
      | linear_combination (-z ^ 6) * h10
      | linear_combination (-z ^ 7) * h10
      | linear_combination (-(1 + z ^ 8)) * h10

