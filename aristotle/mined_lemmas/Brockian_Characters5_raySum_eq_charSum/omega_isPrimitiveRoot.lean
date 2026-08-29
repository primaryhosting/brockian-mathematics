/-
# Ray Sum Eq Char Sum
Category: Characters
Target: Brockian.Characters5.raySum_eq_charSum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ray Sum Eq Char Sum
Category: Characters
Target: Brockian.Characters5.raySum_eq_charSum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace Characters5

open Complex Finset

/-- A primitive fifth root of unity. -/

lemma omega_isPrimitiveRoot : IsPrimitiveRoot omega 5 := by
  simpa [omega] using Complex.isPrimitiveRoot_exp 5 (by norm_num)

