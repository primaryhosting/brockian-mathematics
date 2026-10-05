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

lemma e_zero : e 0 = 1 := by simp [e]

/-- The full character sum over `ZMod 5` vanishes. -/
