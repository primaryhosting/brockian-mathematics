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
The header module docstring above must be the very first thing in this file, so the
file carries no `import` line (Lean requires imports to precede any command).  The
development below is therefore written against Lean core only.  The companion file
`Brockian/SierpinskiCoveringMathlib.lean` imports Mathlib and restates the main
result with Mathlib's `Nat.Prime`.

Statement proved here: `78557` is a Sierpiński number, i.e. `78557 * 2 ^ n + 1` is
composite for every natural number `n`.  The proof uses the classical covering set
of primes `{3, 5, 7, 13, 19, 37, 73}`: the multiplicative order of `2` modulo each of
them divides `36`, and for each residue `r < 36` one of these primes divides
`78557 * 2 ^ r + 1`.
-/

namespace Brockian
namespace SierpinskiCovering

/-- Primality predicate for natural numbers (core-Lean version of `Nat.Prime`). -/
def IsPrimeNat (n : Nat) : Prop := 2 ≤ n ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

/-- The classical covering set of primes for the Sierpiński number `78557`.
The multiplicative order of `2` modulo each of these primes divides `36`. -/
def coveringPrimes : List Nat := [3, 5, 7, 13, 19, 37, 73]

/-- For each prime `p` of the covering set, `2 ^ 36 ≡ 1 (mod p)`. -/
theorem pow_two_36_mod_covering : ∀ p ∈ coveringPrimes, 2 ^ 36 % p = 1 % p := by decide

/-- For each residue `r < 36`, some prime of the covering set divides `78557 * 2 ^ r + 1`. -/
theorem covering_residues :
    ∀ r ∈ List.range 36, ∃ p ∈ coveringPrimes, (78557 * 2 ^ r + 1) % p = 0 := by decide

/-- If `2 ^ 36 ≡ 1 (mod p)` then `2 ^ (36 * q + r) ≡ 2 ^ r (mod p)`. -/
theorem pow_two_period (p r : Nat) (h : 2 ^ 36 % p = 1 % p) :
    ∀ q, 2 ^ (36 * q + r) % p = 2 ^ r % p := by
  intro q
  induction q with
  | zero => simp
  | succ q ih =>
      have e : 36 * (q + 1) + r = (36 * q + r) + 36 := by omega
      rw [e, Nat.pow_add, Nat.mul_mod, ih, h, ← Nat.mul_mod, Nat.mul_one]

/-- Modulo a prime of the covering set, `78557 * 2 ^ n + 1` depends only on `n % 36`. -/
theorem reduce_exponent (p n : Nat) (h : 2 ^ 36 % p = 1 % p) :
    (78557 * 2 ^ n + 1) % p = (78557 * 2 ^ (n % 36) + 1) % p := by
  have key := pow_two_period p (n % 36) h (n / 36)
  rw [Nat.div_add_mod] at key
  rw [Nat.add_mod, Nat.mul_mod, key, ← Nat.mul_mod, ← Nat.add_mod]

/-- For every `n`, some prime of the covering set divides `78557 * 2 ^ n + 1`. -/
theorem exists_covering_divisor (n : Nat) :
    ∃ p ∈ coveringPrimes, p ∣ 78557 * 2 ^ n + 1 := by
  have hr : n % 36 ∈ List.range 36 := List.mem_range.2 (Nat.mod_lt _ (by omega))
  obtain ⟨p, hp, h0⟩ := covering_residues _ hr
  exact ⟨p, hp, Nat.dvd_of_mod_eq_zero ((reduce_exponent p n (pow_two_36_mod_covering p hp)).trans h0)⟩

/-- Every member of the covering set lies strictly between `1` and `74`. -/
theorem coveringPrimes_bounds : ∀ p ∈ coveringPrimes, 1 < p ∧ p ≤ 73 := by decide

/-- `78557 * 2 ^ n + 1` always exceeds every element of the covering set. -/
theorem sierpinski_value_large (n : Nat) : 78558 ≤ 78557 * 2 ^ n + 1 := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have := Nat.mul_le_mul_left 78557 h1
  omega

/-- `78557 * 2 ^ n + 1` has a proper divisor (a divisor `p` with `1 < p < 78557 * 2 ^ n + 1`). -/
theorem sierpinski_proper_divisor (n : Nat) :
    ∃ p, 1 < p ∧ p < 78557 * 2 ^ n + 1 ∧ p ∣ 78557 * 2 ^ n + 1 := by
  obtain ⟨p, hp, hd⟩ := exists_covering_divisor n
  obtain ⟨hp1, hp2⟩ := coveringPrimes_bounds p hp
  have := sierpinski_value_large n
  exact ⟨p, hp1, by omega, hd⟩

/-- **The Sierpiński problem (covering-set instance).**
`78557` is a Sierpiński number: for every natural number `n`, the number
`78557 * 2 ^ n + 1` is not prime. -/
theorem SierpinskiProblem (n : Nat) : ¬ IsPrimeNat (78557 * 2 ^ n + 1) := by
  rintro ⟨-, hdiv⟩
  obtain ⟨p, hp1, hp2, hd⟩ := sierpinski_proper_divisor n
  rcases hdiv p hd with h | h <;> omega

end SierpinskiCovering
end Brockian

import Mathlib
import Brockian.SierpinskiCovering

/-!
# Sierpinski problem, Mathlib restatement

Restates `Brockian.SierpinskiCovering.SierpinskiProblem` using Mathlib's `Nat.Prime`.
-/

namespace Brockian
namespace SierpinskiCovering

/-- The core-Lean primality predicate agrees with Mathlib's `Nat.Prime`. -/
theorem isPrimeNat_iff_prime (n : Nat) : IsPrimeNat n ↔ Nat.Prime n := by
  constructor
  · rintro ⟨h2, hdiv⟩
    exact Nat.prime_def.2 ⟨h2, hdiv⟩
  · intro hp
    exact ⟨hp.two_le, fun m hm => hp.eq_one_or_self_of_dvd m hm⟩

/-- **`78557` is a Sierpiński number**, stated with Mathlib's `Nat.Prime`. -/
theorem sierpinski_not_prime (n : Nat) : ¬ Nat.Prime (78557 * 2 ^ n + 1) := fun hp =>
  SierpinskiProblem n ((isPrimeNat_iff_prime _).2 hp)

end SierpinskiCovering
end Brockian

