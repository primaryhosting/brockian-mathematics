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

/-!
# Sierpinski Problem
Category: Brockian Conjecture
Target: Brockian.SierpinskiCovering.SierpinskiProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This module is deliberately import-free (core Lean 4 only), because Lean does not
allow a module docstring to precede `import` commands.  A companion module
`Brockian.SierpinskiCoveringMathlib` imports Mathlib and restates the main result
using Mathlib's `Nat.Prime`.

Mathematical content: 78557 is a Sierpiński number, i.e. `78557 * 2 ^ n + 1` is
composite for every `n ≥ 1`.  The proof is the classical covering-congruence
argument: every residue class of `n` modulo 36 forces one of the primes
`3, 5, 7, 13, 19, 37, 73` to divide `78557 * 2 ^ n + 1`.
-/

namespace Brockian
namespace SierpinskiCovering

/-- Primality for naturals: `2 ≤ m` and the only divisors of `m` are `1` and `m`.
This is the usual notion; it is proved equivalent to Mathlib's `Nat.Prime` in the
companion module `Brockian.SierpinskiCoveringMathlib`. -/
def IsPrimeNat (m : Nat) : Prop :=
  2 ≤ m ∧ ∀ d : Nat, d ∣ m → d = 1 ∨ d = m

/-- The covering-set assignment: to a residue `r` of `n` modulo `36` it assigns a
prime of the covering set `{3, 5, 7, 13, 19, 37, 73}` that divides
`78557 * 2 ^ r + 1`. -/
def coverPrime (r : Nat) : Nat :=
  if r % 2 = 0 then 3
  else if r % 4 = 1 then 5
  else if r % 3 = 1 then 7
  else if r % 12 = 11 then 13
  else if r % 18 = 15 then 19
  else if r % 9 = 3 then 73
  else 37

/-- The finite verification underlying the covering argument: for each residue
`r < 36` the number `coverPrime r` lies in `[2, 73]`, divides `78557 * 2 ^ r + 1`,
and the multiplicative order of `2` modulo it divides `36`. -/
theorem coverPrime_spec (r : Nat) (hr : r < 36) :
    2 ≤ coverPrime r ∧ coverPrime r ≤ 73 ∧
      (78557 * 2 ^ r + 1) % coverPrime r = 0 ∧ 2 ^ 36 % coverPrime r = 1 := by
  revert r
  decide

/-- Cancelling a factor that is `≡ 1` modulo `p`. -/
theorem mod_cancel_one (p c a b : Nat) (ha : a % p = 1) :
    (c * (a * b) + 1) % p = (c * b + 1) % p := by
  conv => lhs; rw [Nat.add_mod, Nat.mul_mod c (a * b), Nat.mul_mod a b, ha, Nat.one_mul, Nat.mod_mod_of_dvd b (Nat.dvd_refl p)]
  conv => rhs; rw [Nat.add_mod, Nat.mul_mod c b]

/-- Splitting the exponent along division by `36`. -/
theorem two_pow_split (n : Nat) : 2 ^ n = (2 ^ 36) ^ (n / 36) * 2 ^ (n % 36) := by
  rw [← Nat.pow_mul, ← Nat.pow_add]
  congr 1
  omega

/-- For every `n`, the covering prime attached to the residue `n % 36` divides
`78557 * 2 ^ n + 1`. -/
theorem coverPrime_dvd (n : Nat) : coverPrime (n % 36) ∣ 78557 * 2 ^ n + 1 := by
  have h := coverPrime_spec (n % 36) (Nat.mod_lt _ (by omega))
  have hp2 : 2 ≤ coverPrime (n % 36) := h.1
  have hdvd : (78557 * 2 ^ (n % 36) + 1) % coverPrime (n % 36) = 0 := h.2.2.1
  have hord : 2 ^ 36 % coverPrime (n % 36) = 1 := h.2.2.2
  refine Nat.dvd_of_mod_eq_zero ?_
  have hA : (2 ^ 36) ^ (n / 36) % coverPrime (n % 36) = 1 := by
    rw [Nat.pow_mod, hord, Nat.one_pow, Nat.mod_eq_of_lt (by omega)]
  calc (78557 * 2 ^ n + 1) % coverPrime (n % 36)
      = (78557 * ((2 ^ 36) ^ (n / 36) * 2 ^ (n % 36)) + 1) % coverPrime (n % 36) := by
        rw [← two_pow_split]
    _ = (78557 * 2 ^ (n % 36) + 1) % coverPrime (n % 36) :=
        mod_cancel_one _ _ _ _ hA
    _ = 0 := hdvd

/-- **The Sierpiński problem for 78557.**  For every `n ≥ 1` the number
`78557 * 2 ^ n + 1` is not prime.  Hence `78557` is a Sierpiński number.

The proof is the covering-congruence argument modulo `36` with the covering set
`{3, 5, 7, 13, 19, 37, 73}`. -/
theorem SierpinskiProblem : ∀ n : Nat, 1 ≤ n → ¬ IsPrimeNat (78557 * 2 ^ n + 1) := by
  intro n hn hprime
  have h := coverPrime_spec (n % 36) (Nat.mod_lt _ (by omega))
  have hp2 : 2 ≤ coverPrime (n % 36) := h.1
  have hp73 : coverPrime (n % 36) ≤ 73 := h.2.1
  have hdvd := coverPrime_dvd n
  have hbig : 73 < 78557 * 2 ^ n + 1 := by
    have h2 : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    have := Nat.mul_le_mul_left 78557 h2
    omega
  rcases hprime.2 _ hdvd with h1 | h1 <;> omega

/-- Explicit compositeness: for `n ≥ 1` the number `78557 * 2 ^ n + 1` has a
divisor strictly between `1` and itself. -/
theorem sierpinski_composite (n : Nat) (hn : 1 ≤ n) :
    ∃ d : Nat, d ∣ 78557 * 2 ^ n + 1 ∧ 1 < d ∧ d < 78557 * 2 ^ n + 1 := by
  have h := coverPrime_spec (n % 36) (Nat.mod_lt _ (by omega))
  have hbig : 73 < 78557 * 2 ^ n + 1 := by
    have h2 : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    have := Nat.mul_le_mul_left 78557 h2
    omega
  exact ⟨coverPrime (n % 36), coverPrime_dvd n, by omega, by omega⟩

/-- `78557` is odd. -/
theorem odd_78557 : 78557 % 2 = 1 := by decide

end SierpinskiCovering
end Brockian

/-
Companion module to `Brockian.SierpinskiCovering`.

The main module is import-free (Lean does not allow a module docstring before
`import` commands), so it uses its own primality predicate `IsPrimeNat`.  Here we
import Mathlib, show that `IsPrimeNat` agrees with `Nat.Prime`, and restate the
Sierpiński result for `Nat.Prime`.
-/

import Mathlib
import Brockian.SierpinskiCovering

namespace Brockian
namespace SierpinskiCovering

/-- The elementary primality predicate used in the main module coincides with
Mathlib's `Nat.Prime`. -/
theorem isPrimeNat_iff_prime (m : Nat) : IsPrimeNat m ↔ Nat.Prime m :=
  ⟨fun h => Nat.prime_def.2 ⟨h.1, h.2⟩, fun h => ⟨h.two_le, fun d hd => h.eq_one_or_self_of_dvd d hd⟩⟩

/-- **78557 is a Sierpiński number**, stated with Mathlib's `Nat.Prime`:
`78557 * 2 ^ n + 1` is never prime for `n ≥ 1`. -/
theorem sierpinski_78557_not_prime (n : ℕ) (hn : 1 ≤ n) :
    ¬ Nat.Prime (78557 * 2 ^ n + 1) := fun h =>
  SierpinskiProblem n hn ((isPrimeNat_iff_prime _).2 h)

/-- `78557` is odd and `78557 * 2 ^ n + 1` is composite for all `n ≥ 1`. -/
theorem sierpinski_78557 :
    Odd 78557 ∧ ∀ n : ℕ, 1 ≤ n → ¬ Nat.Prime (78557 * 2 ^ n + 1) :=
  ⟨⟨39278, by norm_num⟩, sierpinski_78557_not_prime⟩

end SierpinskiCovering
end Brockian

