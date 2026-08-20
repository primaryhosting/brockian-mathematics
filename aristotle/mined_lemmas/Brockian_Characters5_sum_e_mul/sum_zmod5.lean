/-
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Brockian.Characters5

/-- The primitive fifth root of unity `exp (2πi/5)`. -/

theorem sum_zmod5 (f : ZMod 5 → ℂ) :
    ∑ x : ZMod 5, f x = ∑ k ∈ Finset.range 5, f (k : ZMod 5) := by
  rw [show (∑ x : ZMod 5, f x) = ∑ x : Fin 5, f x from rfl, Fin.sum_univ_five,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

