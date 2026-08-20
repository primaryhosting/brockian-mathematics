import Mathlib

/-!
# Ray Indicator Eq Char Sum
Category: Characters
Target: Brockian.Characters5.rayIndicator_eq_charSum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/

lemma isPrimitiveRoot_omega : IsPrimitiveRoot omega 5 := by
  simpa [omega] using Complex.isPrimitiveRoot_exp 5 (by norm_num)

