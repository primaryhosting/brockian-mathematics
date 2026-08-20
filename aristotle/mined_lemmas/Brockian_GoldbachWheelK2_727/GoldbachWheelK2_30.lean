import Mathlib

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian

/-- The *Goldbach wheel condition of order 2* for a modulus `m`:
every even number `n` is congruent, modulo `m`, to a sum `a + b` of two natural numbers
that are both coprime to `m`.

This is the condition saying that the "wheel" of modulus `m` does not obstruct
Goldbach-type representations of even numbers as sums of two numbers coprime to `m`
(in particular, as sums of two primes not dividing `m`). -/

theorem GoldbachWheelK2_30 : GoldbachWheelK2 30 := goldbachWheelK2_of_pos (by norm_num)

