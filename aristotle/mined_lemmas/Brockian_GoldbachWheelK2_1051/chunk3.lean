/-
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace Brockian

/-! ## Wheel chunks

The verification range `4 ≤ n ≤ 1051` is split into eight blocks of `66` even numbers
(`n = 4 + 2 * (66 * k + m)` with `m < 66`), each discharged by kernel evaluation.
In every case the smaller summand can be taken `≤ 73`, which is the largest least
Goldbach summand occurring in this range. -/


private lemma chunk3 : ∀ m < 66, ∃ p ≤ 73, Nat.Prime p ∧ Nat.Prime (4 + 2 * (66 * 3 + m) - p) := by
  decide

