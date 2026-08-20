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

def GoldbachWheelK2 (m : ℕ) : Prop :=
  ∀ n : ℕ, Even n → ∃ a b : ℕ, Nat.Coprime a m ∧ Nat.Coprime b m ∧ (a + b) % m = n % m

/-- To be coprime to `m` it suffices to share no prime factor with `m`. -/
