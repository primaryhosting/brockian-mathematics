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

lemma twistPartialSum_two : twistPartialSum 2 = 1 + omega := by
  simp [twistPartialSum_eq_geom, Finset.sum_range_succ]

