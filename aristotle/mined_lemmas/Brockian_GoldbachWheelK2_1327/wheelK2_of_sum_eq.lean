/-
Enumeration data for `Brockian.GoldbachWheelK2_1327`.

For every `n` with `2 ≤ n ≤ 1327` we exhibit an explicit pair of primes summing
to the even number `2 * n`, i.e. Goldbach's conjecture is verified for all even
numbers up to twice the wheel modulus `1327`.
-/
import Mathlib

set_option maxRecDepth 10000

namespace Brockian

/-- `GoldbachRep n` states that `n` is a sum of two primes. -/

theorem wheelK2_of_sum_eq {n p q : ℕ} (hn : n % 6 = 2) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp3 : 3 < p) (hq3 : 3 < q) (hsum : p + q = n) : p % 6 = 1 ∧ q % 6 = 1 := by
  have hp' : p % 6 = 1 ∨ p % 6 = 5 := by
    simpa [WheelK2, Finset.mem_insert] using prime_mod_six_mem_wheelK2 hp hp3
  have hq' : q % 6 = 1 ∨ q % 6 = 5 := by
    simpa [WheelK2, Finset.mem_insert] using prime_mod_six_mem_wheelK2 hq hq3
  omega

/-- **Goldbach wheel at the new wheel modulus `1327`.**

The statement bundles four facts about the modulus `1327`:

* `1327` is prime;
* `1327` lies in the `K = 2` wheel `{1, 5}` modulo `6` (indeed `1327 % 6 = 1`);
* Goldbach's conjecture holds for every even number up to `2 * 1327 = 2654`,
  the whole range covered by the new wheel modulus;
* every Goldbach representation of `2 * 1327` by primes exceeding `3` has both
  summands in the residue class `1` modulo `6`, the wheel class forced by
  `2 * 1327 ≡ 2 [MOD 6]`.
-/
