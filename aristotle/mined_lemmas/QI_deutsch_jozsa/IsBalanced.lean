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

def IsBalanced {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  2 * (univ.filter fun x => f x = true).card = 2 ^ n

/-- The all-zeros bit string, i.e. the outcome the algorithm looks for. -/
