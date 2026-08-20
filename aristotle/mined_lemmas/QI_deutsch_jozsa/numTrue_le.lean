/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QI

open Finset

/-- The sign `(-1)^(f x)` attached to a Boolean value. -/

lemma numTrue_le {n : ℕ} (f : (Fin n → Bool) → Bool) : numTrue f ≤ 2 ^ n := by
  rw [numTrue, ← card_domain n]
  exact Finset.card_filter_le _ _

/-- **Deutsch–Jozsa.**  With a single oracle query, the amplitude of the all-zeros
measurement outcome distinguishes constant from balanced functions:
it has modulus `1` exactly when `f` is constant, and vanishes exactly when `f` is
balanced.  In particular the two cases are perfectly distinguished by one query. -/
