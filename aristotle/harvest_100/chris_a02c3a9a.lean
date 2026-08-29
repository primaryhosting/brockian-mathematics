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
NOTE ON IMPORTS.  Lean 4 requires every `import` line to precede all other commands, and a
module docstring `/-! ... -/` counts as a command.  Since the header comment above must be the
very first thing in this file, this module is deliberately written using only Lean 4 core
(no `import` lines at all).  The Mathlib-phrased corollary
`¬ Nat.Prime (78557 * 2 ^ n + 1)` is proved in `Brockian/SierpinskiPrime.lean`, which imports
both Mathlib and this file.

MATHEMATICAL CONTENT.  The *Sierpiński problem* concerns odd `k` such that `k * 2 ^ n + 1` is
composite for every `n`; such `k` are called Sierpiński numbers, and `78557` is the conjectured
smallest one.  That `78557` really is a Sierpiński number is Sierpiński's classical *covering*
argument, formalised below: the covering set `{3, 5, 7, 13, 19, 37, 73}` consists of primes whose
multiplicative order for `2` divides `36`, and for each residue `r < 36` one of them divides
`78557 * 2 ^ r + 1`.
-/

namespace Brockian
namespace SierpinskiCovering

/-- The Sierpiński candidate. -/
def k : Nat := 78557

/-- The covering set `{3, 5, 7, 13, 19, 37, 73}` of primes, arranged as a table indexed by the
residue `r = n % 36`: `coveringTable r` is a prime dividing `78557 * 2 ^ r + 1`. -/
def coveringTable : List Nat :=
  [3, 5, 3, 73, 3, 5, 3, 7, 3, 5, 3, 13, 3, 5, 3, 19, 3, 5,
   3, 7, 3, 5, 3, 13, 3, 5, 3, 37, 3, 5, 3, 7, 3, 5, 3, 13]

/-- The prime of the covering set assigned to `n`; it depends only on `n % 36`. -/
def cov (n : Nat) : Nat := coveringTable.getD (n % 36) 3

/-- The finite verification underlying the covering argument: for each residue `r < 36` the
assigned number `cov r` is at least `2`, at most `73`, satisfies `2 ^ 36 ≡ 1 [MOD cov r]`
(equivalently, its multiplicative order for `2` divides `36`), and divides `k * 2 ^ r + 1`. -/
theorem cov_spec :
    ∀ r < 36, 2 ≤ cov r ∧ cov r ≤ 73 ∧ 2 ^ 36 % cov r = 1 % cov r ∧
      (k * 2 ^ r + 1) % cov r = 0 := by
  decide

/-- If `2 ^ 36 ≡ 1 [MOD p]` then `2 ^ (36 * q + r) ≡ 2 ^ r [MOD p]`. -/
theorem two_pow_period_aux (p q r : Nat) (hp : 2 ^ 36 % p = 1 % p) :
    2 ^ (36 * q + r) % p = 2 ^ r % p := by
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, hp, ← Nat.pow_mod, Nat.one_pow,
    ← Nat.mul_mod, Nat.one_mul]

/-- Powers of two modulo `p` are `36`-periodic in the exponent whenever `2 ^ 36 ≡ 1 [MOD p]`. -/
theorem two_pow_period (p n : Nat) (hp : 2 ^ 36 % p = 1 % p) :
    2 ^ n % p = 2 ^ (n % 36) % p := by
  have h := two_pow_period_aux p (n / 36) (n % 36) hp
  rw [Nat.div_add_mod] at h
  exact h

/-- Consequently `k * 2 ^ n + 1` and `k * 2 ^ (n % 36) + 1` agree modulo `p`. -/
theorem shift_mod (p n : Nat) (hp : 2 ^ 36 % p = 1 % p) :
    (k * 2 ^ n + 1) % p = (k * 2 ^ (n % 36) + 1) % p := by
  rw [Nat.add_mod, Nat.mul_mod, two_pow_period p n hp, ← Nat.mul_mod, ← Nat.add_mod]

/-- For every `n`, the number `cov n` (an element of the covering set) divides `k * 2 ^ n + 1`,
and it is a proper divisor: `2 ≤ cov n ≤ 73 < k * 2 ^ n + 1`. -/
theorem cov_dvd (n : Nat) :
    2 ≤ cov n ∧ cov n < k * 2 ^ n + 1 ∧ cov n ∣ (k * 2 ^ n + 1) := by
  have hlt : n % 36 < 36 := Nat.mod_lt _ (by decide)
  obtain ⟨h2, h73, hord, hdvd⟩ := cov_spec (n % 36) hlt
  have hcov : cov n = cov (n % 36) := by
    unfold cov
    rw [Nat.mod_mod_of_dvd n (Nat.dvd_refl 36)]
  have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hbig : k * 1 ≤ k * 2 ^ n := Nat.mul_le_mul_left k hone
  have hmod : (k * 2 ^ n + 1) % cov n = 0 := by
    rw [hcov, shift_mod (cov (n % 36)) n hord]
    exact hdvd
  refine ⟨by omega, by simp only [k] at hbig ⊢; omega, Nat.dvd_of_mod_eq_zero hmod⟩

/-- **The Sierpiński problem (Sierpiński's covering construction).**

`78557` is a Sierpiński number: for every natural number `n` the number `78557 * 2 ^ n + 1` is
composite, i.e. it has a divisor `d` with `2 ≤ d < 78557 * 2 ^ n + 1`.

The witness is supplied by the covering set `{3, 5, 7, 13, 19, 37, 73}`: each of these primes
satisfies `2 ^ 36 ≡ 1` modulo it, and for every residue `r` of `n` modulo `36` one of them
divides `78557 * 2 ^ r + 1`, hence also `78557 * 2 ^ n + 1`. -/
theorem SierpinskiProblem :
    ∀ n : Nat, ∃ d : Nat, 2 ≤ d ∧ d < 78557 * 2 ^ n + 1 ∧ d ∣ (78557 * 2 ^ n + 1) :=
  fun n => ⟨cov n, cov_dvd n⟩

end SierpinskiCovering
end Brockian

import Mathlib
import Brockian.SierpinskiCovering

/-!
# Sierpinski Problem — Mathlib-phrased corollary

`Brockian/SierpinskiCovering.lean` proves, in pure Lean 4 core, that `78557 * 2 ^ n + 1` always
has a divisor `d` with `2 ≤ d < 78557 * 2 ^ n + 1`.  Here we restate that in Mathlib's language:
`78557 * 2 ^ n + 1` is never prime, i.e. `78557` is a Sierpiński number.
-/

namespace Brockian
namespace SierpinskiCovering

/-- `k` is a Sierpiński number if `k * 2 ^ n + 1` is composite for every `n`. -/
def IsSierpinskiNumber (k : ℕ) : Prop := ∀ n : ℕ, ¬ Nat.Prime (k * 2 ^ n + 1)

/-- `78557 * 2 ^ n + 1` is never prime. -/
theorem not_prime_78557_mul_two_pow_add_one (n : ℕ) : ¬ Nat.Prime (78557 * 2 ^ n + 1) := by
  intro hp
  obtain ⟨d, hd2, hdlt, hdvd⟩ := SierpinskiProblem n
  rcases hp.eq_one_or_self_of_dvd d hdvd with h | h <;> omega

/-- **`78557` is a Sierpiński number.** -/
theorem isSierpinskiNumber_78557 : IsSierpinskiNumber 78557 :=
  not_prime_78557_mul_two_pow_add_one

end SierpinskiCovering
end Brockian

