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
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` lines to precede any module docstring, so the header comment above is a
plain block comment and is repeated here as the module docstring.)
-/

open ArithmeticFunction

namespace Brockian.BetrothedNumbers

/-- Two positive integers `m ≠ n` are *betrothed* (a quasi-amicable pair) when the sum of the
divisors of each equals `m + n + 1`; equivalently, the sum of the divisors of each strictly
between `1` and the number itself equals the other number. -/

theorem sigma_even_of_odd_prime_mul {p k : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hk : Nat.Coprime p k) : Even (sigma 1 (p * k)) := by
  have hmul : sigma 1 (p * k) = sigma 1 p * sigma 1 k :=
    (isMultiplicative_sigma (k := 1)).map_mul_of_coprime hk
  have hsp : sigma 1 p = p + 1 := by
    simp [sigma_one_apply, hp.divisors, Finset.sum_pair hp.one_lt.ne, Nat.add_comm]
  rw [hmul, hsp]
  exact (Nat.even_add_one.2 (Nat.not_even_iff_odd.2 hodd)).mul_right _

/-- **Structural obstruction.** If the two members of a betrothed pair have the same parity, then
no odd prime can divide the second member to the first power exactly. -/
