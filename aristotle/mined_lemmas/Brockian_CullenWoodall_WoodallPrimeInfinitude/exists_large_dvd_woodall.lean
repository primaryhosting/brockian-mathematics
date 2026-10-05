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
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Header kept verbatim, except that it is a plain block comment `/- -/` rather than a
-- module docstring `/-! -/`: Lean 4 does not allow any command, including a module
-- docstring, to precede the `import` section of a file.)

import Mathlib

namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; for `n ≥ 1`
this agrees with the usual integer definition). -/

theorem exists_large_dvd_woodall (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (N : ℕ) :
    ∃ n, N < n ∧ p ∣ woodall n := by
  haveI := Fact.mk hp
  have hp2 : 2 ≤ p := hp.two_le
  have hpodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hodd
  have hp3 : 3 ≤ p := by omega
  set q : ℕ := (p + 1) / 2 with hq
  have h2q : 2 * q = p + 1 := by omega
  set t : ℕ := N + 1 with ht
  set k : ℕ := q + t * p with hk
  set n : ℕ := 1 + k * (p - 1) with hn
  have hn1 : 1 ≤ n := by omega
  have hNn : N < n := by
    have h1 : t ≤ k := by nlinarith [Nat.zero_le q]
    have h2 : k ≤ k * (p - 1) := Nat.le_mul_of_pos_right k (by omega)
    omega
  refine ⟨n, hNn, ?_⟩
  have hpne : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have hnd : ¬ (p ∣ 2) := fun h => hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    intro hh
    exact hnd ((ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast hh))
  have hpm1 : ((p - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub hp.one_le, hpne]; simp
  have h2k : (2 : ZMod p) * (k : ZMod p) = 1 := by
    have h1 : 2 * k = (p + 1) + 2 * t * p := by rw [hk]; ring_nf; omega
    have h2 : ((2 * k : ℕ) : ZMod p) = ((p + 1 + 2 * t * p : ℕ) : ZMod p) := by rw [h1]
    push_cast [hpne] at h2
    rw [h2]; ring
  have hncast : ((n : ℕ) : ZMod p) = 1 - (k : ZMod p) := by
    rw [hn]; push_cast [hpm1]; ring
  have hpow : (2 : ZMod p) ^ n = 2 := by
    have hfermat : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
    calc (2 : ZMod p) ^ n = 2 ^ (1 + k * (p - 1)) := by rw [hn]
    _ = 2 * ((2 : ZMod p) ^ (p - 1)) ^ k := by rw [pow_add, ← pow_mul, mul_comm k (p - 1)]; ring
    _ = 2 := by rw [hfermat]; simp
  have key : ((n * 2 ^ n : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    push_cast
    rw [hncast, hpow]
    linear_combination -h2k
  have hmod : (1 : ℕ) ≡ n * 2 ^ n [MOD p] := ((ZMod.natCast_eq_natCast_iff _ _ _).mp key).symm
  have hge : 1 ≤ n * 2 ^ n := Nat.mul_pos (by omega) (Nat.two_pow_pos n)
  exact (Nat.modEq_iff_dvd' hge).mp hmod

end Divisors

/-!
### The main reduction

Whether there are infinitely many Woodall primes is an open problem, so the statement below
is a *conditional reduction*: the infinitude of the set of Woodall primes is proved
equivalent to the statement that the index set `{n | (n * 2 ^ n - 1).Prime}` is unbounded.
-/

/-- **Woodall prime infinitude (conditional reduction).**
The set of Woodall primes is infinite if and only if there are arbitrarily large indices `n`
for which the Woodall number `n * 2 ^ n - 1` is prime. -/
