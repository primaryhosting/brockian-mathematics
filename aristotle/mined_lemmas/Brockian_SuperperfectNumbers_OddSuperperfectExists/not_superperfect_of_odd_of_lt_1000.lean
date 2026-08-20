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

/-
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A natural number `n` is *superperfect* when `σ(σ(n)) = 2n`. Whether an odd superperfect
number exists is an open problem, so the target result
`Brockian.SuperperfectNumbers.OddSuperperfectExists` is a Lean-checked *conditional
reduction*: the existence of an odd superperfect number is equivalent to the existence of
one satisfying a list of proved necessary conditions (size lower bound from a kernel
computation, deficiency bounds, non-divisibility by `3` in the non-square case, and parity
information in the square case).
-/

namespace Brockian.SuperperfectNumbers

open Finset

/-- The sum-of-divisors function `σ(n) = ∑_{d ∣ n} d`. -/

theorem not_superperfect_of_odd_of_lt_1000 {n : ℕ} (hodd : Odd n) (hn : n < 1000) :
    ¬ Superperfect n := by
  rintro ⟨-, heq⟩
  have h2 : n % 2 = 1 := Nat.odd_iff.mp hodd
  rcases Nat.lt_or_ge n 250 with h | h
  · exact check_lt_250 n (Finset.mem_Ico.mpr ⟨Nat.zero_le _, h⟩) h2 heq
  rcases Nat.lt_or_ge n 500 with h' | h'
  · exact check_lt_500 n (Finset.mem_Ico.mpr ⟨h, h'⟩) h2 heq
  rcases Nat.lt_or_ge n 750 with h'' | h''
  · exact check_lt_750 n (Finset.mem_Ico.mpr ⟨h', h''⟩) h2 heq
  · exact check_lt_1000 n (Finset.mem_Ico.mpr ⟨h'', hn⟩) h2 heq

end FiniteCheck

/-- **Conditional reduction for the existence of an odd superperfect number.**

An odd superperfect number exists if and only if there is one satisfying all of the
following necessary conditions: it is at least `1000`, it is deficient (`n < σ(n) < 2n`),
and unless it is a perfect square it is strongly deficient (`3σ(n) + 2 ≤ 4n`) and not
divisible by `3`; while if it is a perfect square, `σ(n)` is odd and is not a square. -/
