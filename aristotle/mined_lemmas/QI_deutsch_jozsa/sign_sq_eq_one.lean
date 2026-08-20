import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Statement: Deutsch–Jozsa decides constant-vs-balanced with one query.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Finset

/-- The sign `(-1)^b` attached to a boolean. -/

lemma sign_sq_eq_one (b : Bool) : sign b * sign b = 1 := by cases b <;> norm_num [sign]

/-- The final state of the circuit is a unit vector: the outcome probabilities
`(amp f y) ^ 2` sum to `1`. -/
