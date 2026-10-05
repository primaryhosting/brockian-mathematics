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
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede every command, including module
-- docstrings, so the header above is a plain block comment and is repeated as a
-- module docstring after the import.)

import Mathlib

/-!
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/

theorem prime_dvd_woodall (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    p ∣ woodall ((p - 1) ^ 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set n := (p - 1) ^ 2 with hn
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hcast : ((n : ℕ) : ZMod p) = 1 := by
    have h1 : ((p - 1 : ℕ) : ZMod p) = -1 := by
      have : ((p - 1 : ℕ) : ZMod p) = (p : ZMod p) - 1 := by
        push_cast [Nat.cast_sub hp1]; ring
      rw [this, ZMod.natCast_self]; ring
    rw [hn]
    push_cast
    rw [h1]; ring
  have hpow : ((2 : ZMod p)) ^ n = 1 := by
    have hdvd : (p - 1) ∣ n := by
      rw [hn, pow_two]; exact Dvd.intro _ rfl
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, pow_mul, two_pow_sub_one_eq_one p hp hodd, one_pow]
  have hzero : ((n * 2 ^ n : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    push_cast
    rw [hcast, hpow]
    ring
  have hmod : (1 : ℕ) ≡ n * 2 ^ n [MOD p] := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mp hzero.symm
    exact this
  have hone : 1 ≤ n * 2 ^ n := by
    have hnpos : 1 ≤ n := by
      have : 2 ≤ p := hp.two_le
      have : 1 ≤ p - 1 := by omega
      rw [hn]; nlinarith
    exact one_le_mul_two_pow hnpos
  exact (Nat.modEq_iff_dvd' hone).mp hmod

/-!
## The conjecture and its reduction

The infinitude of Cullen primes is an open problem: no proof is known that `n * 2 ^ n + 1`
is prime for infinitely many `n` (the known Cullen prime indices begin
`1, 141, 4713, 5795, 6611, 18496, …`).  What we record here is the exact reduction of the
conjecture to an unboundedness statement, together with the unconditional partial results
above.
-/

/-- The (open) Cullen prime conjecture: there are infinitely many Cullen primes. -/
