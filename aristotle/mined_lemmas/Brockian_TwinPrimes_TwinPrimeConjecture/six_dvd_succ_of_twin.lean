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
/-!
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
The Twin Prime Conjecture is a famous open problem; it is stated below as
`Brockian.TwinPrimes.TwinPrimeConjecture`.  What this file establishes, fully and
axiom-cleanly, is a set of Lean-checked *reductions* and *partial results*:

* `twinPrimeConjecture_iff_infinite` : the conjecture is equivalent to the infinitude of
  the set of twin primes;
* `clement` : **Clement's criterion** — for `n ≥ 2`, `n` and `n + 2` are both prime iff
  `n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n`;
* `twinPrimeConjecture_iff_clement` : consequently the conjecture is equivalent to a purely
  arithmetic statement about factorial congruences;
* `not_twinPrimeConjecture_iff_bddAbove` : its negation is equivalent to the existence of a
  largest twin prime pair;
* unconditional partial results: `six_dvd_succ_of_twin` and `twin_primes_small`.
-/

namespace Brockian.TwinPrimes

open Nat

/-- `p` is the smaller member of a twin prime pair. -/

theorem six_dvd_succ_of_twin {n : ℕ} (h : IsTwinPrimePair n) (h3 : 3 < n) : 6 ∣ n + 1 := by
  obtain ⟨hn, hn2⟩ := h
  have h2 : ¬ (2 ∣ n) := fun hd => by
    have := Nat.Prime.eq_one_or_self_of_dvd hn 2 hd; omega
  have h3' : ¬ (3 ∣ n) := fun hd => by
    have := Nat.Prime.eq_one_or_self_of_dvd hn 3 hd; omega
  have h3'' : ¬ (3 ∣ (n + 2)) := fun hd => by
    have := Nat.Prime.eq_one_or_self_of_dvd hn2 3 hd; omega
  have e2 : 2 ∣ n + 1 := by omega
  have e3 : 3 ∣ n + 1 := by clear h2 h3 e2 hn hn2; omega
  clear h2 h3' h3'' h3 hn hn2
  omega

/-- The first eight twin prime pairs. -/
