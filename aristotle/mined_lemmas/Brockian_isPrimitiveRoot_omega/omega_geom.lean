import Mathlib

/-!
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/

theorem omega_geom : 1 + omega + omega ^ 2 + omega ^ 3 + omega ^ 4 = 0 := by
  have h := sum_omega_pow
  simp [Finset.sum_range_succ] at h
  linear_combination h

/-- Expansion of a sum over `ZMod 5` into its five terms. -/
