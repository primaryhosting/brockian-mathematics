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

import Mathlib
import Brockian.RieselCovering

/-!
# Riesel Problem — Mathlib interface

Companion to `Brockian.RieselCovering` (which is import-free): the same result phrased with
Mathlib's `Nat.Prime`.
-/

namespace Brockian
namespace RieselCovering

/-- `509203 * 2 ^ n - 1` is not prime for any `n ≥ 1`, stated with `Nat.Prime`. -/
theorem not_nat_prime (n : ℕ) (hn : 1 ≤ n) : ¬ Nat.Prime (509203 * 2 ^ n - 1) := by
  intro hp
  obtain ⟨d, h1, h2, h3⟩ := RieselProblem n hn
  rcases hp.eq_one_or_self_of_dvd d h3 with h | h <;> omega

end RieselCovering
end Brockian

/-!
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
A *Riesel number* is an odd `k` such that `k * 2 ^ n - 1` is composite for every `n ≥ 1`.
This file exhibits Riesel's original witness `k = 509203` together with the covering
congruence argument that proves it, and derives that `509203 * 2 ^ n - 1` is composite
for all `n ≥ 1`.

The argument.  Each of the primes `3, 5, 7, 13, 17, 241` divides
`2 ^ 24 - 1 = 16777215 = 3 ^ 2 * 5 * 7 * 13 * 17 * 241`, so modulo each of them the powers
of two are periodic with period dividing `24`.  A direct finite check shows that for every
residue `r < 24` one of these primes divides `509203 * 2 ^ r - 1`; the table is recorded in
`Brockian.RieselCovering.coveringTable`.  Periodicity (`dvd_shift`, `dvd_shift_iter`) then
propagates each of these divisibilities to all `n` congruent to `r` modulo `24`.

The file is deliberately self-contained: it uses no imports, so all arithmetic facts are
proved from Lean core (`decide`, `omega`) only.
-/

namespace Brockian
namespace RieselCovering

/-- Riesel's witness `k = 509203`. -/
def k : Nat := 509203

/-- For each residue `r < 24`, a prime from the covering set `{3, 5, 7, 13, 17, 241}`
that divides `509203 * 2 ^ r - 1`.  The entry at index `r` is used for all `n ≡ r [MOD 24]`. -/
def coveringTable : List Nat :=
  [3, 5, 3, 241, 3, 5, 3, 13, 3, 5, 3, 7, 3, 5, 3, 17, 3, 5, 3, 13, 3, 5, 3, 7]

/-- The divisor of `k * 2 ^ n - 1` supplied by the covering congruences. -/
def coveringDivisor (n : Nat) : Nat := coveringTable.getD (n % 24) 3

set_option maxRecDepth 10000 in
/-- The finite verification underlying the covering argument: for every residue `r < 24`
the tabulated divisor is a nontrivial divisor of `2 ^ 24 - 1 = 16777215` and of
`509203 * 2 ^ r - 1`. -/
theorem coveringTable_spec :
    ∀ r, r < 24 →
      1 < coveringTable.getD r 3 ∧ coveringTable.getD r 3 ≤ 241 ∧
        coveringTable.getD r 3 ∣ 16777215 ∧
        coveringTable.getD r 3 ∣ k * 2 ^ r - 1 := by
  decide

/-- Periodicity step: since `p ∣ 2 ^ 24 - 1`, divisibility of `k * 2 ^ n - 1` by `p`
propagates from `n` to `n + 24`. -/
theorem dvd_shift {p n : Nat} (h24 : p ∣ 16777215) (h : p ∣ k * 2 ^ n - 1) :
    p ∣ k * 2 ^ (n + 24) - 1 := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := h24
  have hx : 0 < k * 2 ^ n := Nat.mul_pos (by decide) (Nat.two_pow_pos n)
  have hp : (2 : Nat) ^ (n + 24) = 2 ^ n * 16777216 := by rw [Nat.pow_add]
  refine ⟨16777216 * a + b, ?_⟩
  have key : p * (16777216 * a + b) = 16777216 * (p * a) + p * b := by
    rw [Nat.mul_add, Nat.mul_left_comm]
  rw [hp, key, ← ha, ← hb]
  unfold k at *
  omega

/-- Iterated form of `dvd_shift`. -/
theorem dvd_shift_iter {p r : Nat} (h24 : p ∣ 16777215) (h0 : p ∣ k * 2 ^ r - 1) :
    ∀ q, p ∣ k * 2 ^ (r + 24 * q) - 1 := by
  intro q
  induction q with
  | zero => simpa using h0
  | succ q ih =>
      have e : r + 24 * (q + 1) = (r + 24 * q) + 24 := by omega
      rw [e]
      exact dvd_shift h24 ih

/-- **The covering property**: for every `n`, `coveringDivisor n` is a divisor of
`509203 * 2 ^ n - 1` lying strictly between `1` and `242`. -/
theorem coveringDivisor_spec (n : Nat) :
    1 < coveringDivisor n ∧ coveringDivisor n ≤ 241 ∧ coveringDivisor n ∣ k * 2 ^ n - 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := coveringTable_spec (n % 24) (Nat.mod_lt n (by decide))
  refine ⟨h1, h2, ?_⟩
  have hn : n % 24 + 24 * (n / 24) = n := Nat.mod_add_div n 24
  have := dvd_shift_iter (p := coveringDivisor n) h3 h4 (n / 24)
  rwa [hn] at this

/-- **The Riesel problem (Riesel's witness `k = 509203`).**
For every `n ≥ 1` the number `509203 * 2 ^ n - 1` is composite: it admits a divisor `d`
with `1 < d < 509203 * 2 ^ n - 1`.  Hence `509203` is a Riesel number. -/
theorem RieselProblem (n : Nat) (hn : 1 ≤ n) :
    ∃ d, 1 < d ∧ d < 509203 * 2 ^ n - 1 ∧ d ∣ 509203 * 2 ^ n - 1 := by
  obtain ⟨h1, h2, h3⟩ := coveringDivisor_spec n
  have hpow : (2 : Nat) ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  have hbig : 509203 * 2 ≤ 509203 * 2 ^ n := Nat.mul_le_mul_left 509203 (by simpa using hpow)
  refine ⟨coveringDivisor n, h1, ?_, h3⟩
  unfold k at h3
  omega

/-- Restatement: for `n ≥ 1` the number `509203 * 2 ^ n - 1` is never prime.  Primality is
spelled out explicitly here, so that the statement is independent of any library
definition; see `Brockian.RieselCoveringPrime` for the version using `Nat.Prime`. -/
theorem RieselProblem_not_prime (n : Nat) (hn : 1 ≤ n) :
    ¬ (2 ≤ 509203 * 2 ^ n - 1 ∧
        ∀ d, d ∣ 509203 * 2 ^ n - 1 → d = 1 ∨ d = 509203 * 2 ^ n - 1) := by
  rintro ⟨-, hd⟩
  obtain ⟨d, h1, h2, h3⟩ := RieselProblem n hn
  rcases hd d h3 with h | h <;> omega

end RieselCovering
end Brockian

