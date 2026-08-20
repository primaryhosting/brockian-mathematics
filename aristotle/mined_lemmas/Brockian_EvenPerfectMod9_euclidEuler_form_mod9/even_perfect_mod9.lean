import Mathlib
import PerfectNumbersEuler

namespace Brockian.EvenPerfectMod9

open Nat

/-- The modular-arithmetic consequence of the Euclid–Euler form of an even perfect number. -/

theorem even_perfect_mod9 {n : ℕ} (he : Even n) (hp : Nat.Perfect n) (h6 : 6 < n) : n % 9 = 1 := by
  obtain ⟨k, hprime, rfl⟩ :=
    PerfectNumbersEuler.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect he hp
  exact euclidEuler_form_mod9 hprime h6

end Brockian.EvenPerfectMod9

/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.Tactic.NormNum.Prime

/-!
# Perfect Numbers

This file proves Theorem 70 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

The theorem characterizes even perfect numbers.

Euclid proved that if `2 ^ (k + 1) - 1` is prime (these primes are known as Mersenne primes),
  then `2 ^ k * (2 ^ (k + 1) - 1)` is perfect.

Euler proved the converse, that if `n` is even and perfect, then there exists `k` such that
  `n = 2 ^ k * (2 ^ (k + 1) - 1)` and `2 ^ (k + 1) - 1` is prime.

## References
https://en.wikipedia.org/wiki/Euclid%E2%80%93Euler_theorem
-/


namespace PerfectNumbersEuler

namespace Nat

open ArithmeticFunction Finset

-- access notation `σ`
open scoped sigma

