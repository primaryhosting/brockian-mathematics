/-
# Parseval
Category: Characters
Target: Brockian.Characters5.parseval
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/

lemma omega_ne_one : omega ≠ 1 :=
  (Complex.isPrimitiveRoot_exp 5 (by norm_num)).ne_one (by norm_num)

