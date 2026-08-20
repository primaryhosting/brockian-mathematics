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

