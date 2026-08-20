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

private lemma dvd_iff_of_modEq {m a r : ℕ} (h : a ≡ r [MOD m]) : m ∣ a ↔ m ∣ r := by
  constructor <;> intro hd
  · exact Nat.modEq_zero_iff_dvd.1 (h.symm.trans (Nat.modEq_zero_iff_dvd.2 hd))
  · exact Nat.modEq_zero_iff_dvd.1 (h.trans (Nat.modEq_zero_iff_dvd.2 hd))

/-- Local admissibility at a prime `Q` not dividing the common difference `M`:
one can choose `x` so that neither `M * x + a` nor `M * x + a + n` is divisible by `Q`
(here `n` is even, which is what rules out the obstruction at `Q = 2`). -/
