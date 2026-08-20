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

private lemma chunk0 : ∀ m < 66, ∃ p ≤ 73, Nat.Prime p ∧ Nat.Prime (4 + 2 * (66 * 0 + m) - p) := by
  decide

private lemma chunk1 : ∀ m < 66, ∃ p ≤ 73, Nat.Prime p ∧ Nat.Prime (4 + 2 * (66 * 1 + m) - p) := by
  decide

private lemma chunk2 : ∀ m < 66, ∃ p ≤ 73, Nat.Prime p ∧ Nat.Prime (4 + 2 * (66 * 2 + m) - p) := by
  decide

private lemma chunk3 : ∀ m < 66, ∃ p ≤ 73, Nat.Prime p ∧ Nat.Prime (4 + 2 * (66 * 3 + m) - p) := by
  decide

private lemma chunk4 : ∀ m < 66, ∃ p ≤ 73, Nat.Prime p ∧ Nat.Prime (4 + 2 * (66 * 4 + m) - p) := by
  decide

private lemma chunk5 : ∀ m < 66, ∃ p ≤ 73, Nat.Prime p ∧ Nat.Prime (4 + 2 * (66 * 5 + m) - p) := by
  decide

private lemma chunk6 : ∀ m < 66, ∃ p ≤ 73, Nat.Prime p ∧ Nat.Prime (4 + 2 * (66 * 6 + m) - p) := by
  decide

private lemma chunk7 : ∀ m < 66, ∃ p ≤ 73, Nat.Prime p ∧ Nat.Prime (4 + 2 * (66 * 7 + m) - p) := by
  decide

/-- Assembled wheel: for every `m < 524` the even number `4 + 2 * m` has a prime
summand `p ≤ 73` with prime complement. -/
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
theorem GoldbachWheelK2_1051 :
    ∀ n : ℕ, 4 ≤ n → n ≤ 1051 → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  intro n h4 h1051 hev
  obtain ⟨t, ht⟩ := hev
  have hm : (n - 4) / 2 < 524 := by omega
  obtain ⟨p, hp73, hp, hq⟩ := wheel_key ((n - 4) / 2) hm
  have hn : 4 + 2 * ((n - 4) / 2) = n := by omega
  rw [hn] at hq
  have h2 := hq.two_le
  refine ⟨p, n - p, hp, hq, by omega⟩

end Brockian

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

