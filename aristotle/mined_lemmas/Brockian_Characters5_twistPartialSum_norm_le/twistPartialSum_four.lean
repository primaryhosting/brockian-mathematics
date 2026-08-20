/-!
# Twist Partial Sum Norm Le
Category: Characters
Target: Brockian.Characters5.twistPartialSum_norm_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/

lemma twistPartialSum_four : twistPartialSum 4 = -(omega ^ 4) := by
  have h := sum_omega_pow
  simp only [twistPartialSum_eq_geom, Finset.sum_range_succ, Finset.sum_range_zero]
  linear_combination h

/-- Bounded partial sums of the zero-mean twist: `‖∑_{n < N} e (n mod 5)‖ ≤ 2` for every `N`. -/
