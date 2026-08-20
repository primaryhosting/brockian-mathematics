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
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
Polignac's conjecture ("for every even `n > 0` there are infinitely many pairs of
*consecutive* primes whose difference is `n`") is a well-known open problem, and it is
not available in Mathlib.  What is proved here is a *conditional reduction*: Polignac's
conjecture follows from the two-linear-form case of Dickson's conjecture.

The reduction itself is unconditional Lean-checked mathematics:

* pick `n - 1` distinct primes `q 0, …, q (n-2)`, all larger than `n`;
* by the Chinese Remainder Theorem choose `a` with `a ≡ -(i+1) [MOD q i]`;
* with `M = ∏ q i`, every number of the form `M * x + a + (i+1)` is divisible by `q i`,
  hence composite once it exceeds `q i`;
* the pair of linear forms `M * x + a`, `M * x + (a + n)` is admissible, so Dickson's
  conjecture supplies arbitrarily large `x` making both values prime.  Those two primes
  are then *consecutive* primes differing by exactly `n`.
-/

namespace Brockian.PolignacPrimes

/-- `n` is a Polignac gap: there are arbitrarily large primes `p` such that `p + n` is
prime and no number strictly between `p` and `p + n` is prime, i.e. `p` and `p + n` are
consecutive primes at distance `n`. -/

private lemma exists_x_not_dvd {Q M a n : ℕ} (hQ : Nat.Prime Q) (hM : ¬ Q ∣ M)
    (hn : Even n) : ∃ x : ℕ, ¬ Q ∣ (M * x + a) ∧ ¬ Q ∣ (M * x + a + n) := by
  haveI : Fact (Nat.Prime Q) := ⟨hQ⟩
  haveI : NeZero Q := ⟨hQ.ne_zero⟩
  have hv : ∃ v : ZMod Q, v ≠ 0 ∧ v + (n : ZMod Q) ≠ 0 := by
    by_cases h1 : (1 : ZMod Q) + (n : ZMod Q) = 0
    · refine ⟨2, ?_, ?_⟩
      · by_cases hQ2 : Q = 2
        · subst hQ2
          have hn2 : ((n : ℕ) : ZMod 2) = 0 := by
            refine (ZMod.natCast_eq_zero_iff n 2).2 ?_
            obtain ⟨k, hk⟩ := hn
            omega
          rw [hn2, add_zero] at h1
          exact absurd h1 one_ne_zero
        · have h2 : (2 : ZMod Q) = ((2 : ℕ) : ZMod Q) := by push_cast; ring
          rw [h2]
          intro hc
          exact hQ2 ((Nat.prime_dvd_prime_iff_eq hQ Nat.prime_two).1
            ((ZMod.natCast_eq_zero_iff 2 Q).1 hc))
      · have h2 : (2 : ZMod Q) + (n : ZMod Q) = ((1 : ZMod Q) + (n : ZMod Q)) + 1 := by ring
        rw [h2, h1, zero_add]
        exact one_ne_zero
    · exact ⟨1, one_ne_zero, h1⟩
  obtain ⟨v, hv0, hvn⟩ := hv
  have hMne : (M : ZMod Q) ≠ 0 := fun h => hM ((ZMod.natCast_eq_zero_iff M Q).1 h)
  set x : ℕ := ((v - (a : ZMod Q)) * (M : ZMod Q)⁻¹).val with hxdef
  have hcast : ((M * x + a : ℕ) : ZMod Q) = v := by
    push_cast
    rw [hxdef, ZMod.natCast_val, ZMod.cast_id]
    field_simp
    exact sub_add_cancel v (a : ZMod Q)
  refine ⟨x, ?_, ?_⟩
  · intro hd
    rw [← ZMod.natCast_eq_zero_iff, hcast] at hd
    exact hv0 hd
  · intro hd
    rw [← ZMod.natCast_eq_zero_iff] at hd
    push_cast at hd
    rw [show ((M : ZMod Q) * (x : ZMod Q) + (a : ZMod Q)) = ((M * x + a : ℕ) : ZMod Q) by
      push_cast; ring, hcast] at hd
    exact hvn hd

/-- **Polignac's conjecture, conditionally on the two-form case of Dickson's
conjecture.**  Assuming `DicksonPairHypothesis`, for every positive even `n` there are
arbitrarily large pairs of consecutive primes `p < p + n`. -/
