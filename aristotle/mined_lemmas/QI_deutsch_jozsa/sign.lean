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

def sign (b : Bool) : ℝ := if b then -1 else 1

/-- The phase `(-1)^(x ⬝ y)` coming from the final layer of Hadamard gates,
written as the product of the bitwise contributions. -/
