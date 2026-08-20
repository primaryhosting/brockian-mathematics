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


private lemma wheel_key :
    ∀ m < 524, ∃ p ≤ 73, Nat.Prime p ∧ Nat.Prime (4 + 2 * m - p) := by
  intro m hm
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 66 ∧ m = 66 * k + r :=
    ⟨m / 66, m % 66, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 66).symm⟩
  have hk : k < 8 := by omega
  interval_cases k
  · exact chunk0 r hr
  · exact chunk1 r hr
  · exact chunk2 r hr
  · exact chunk3 r hr
  · exact chunk4 r hr
  · exact chunk5 r hr
  · exact chunk6 r hr
  · exact chunk7 r hr

/-- **Goldbach wheel, K = 2, modulus 1051.**
Every even natural number `n` with `4 ≤ n ≤ 1051` is a sum of two primes. -/
