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
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Overview

The *spectral model* of the Goldbach problem attaches to every natural number `n` the
"spectral count"
```
spectralCount n = ∑_{p ≤ n} [ p prime ] · [ n - p prime ]
```
i.e. the number of representations of `n` as an ordered sum of two primes.  The *spectral
model hypothesis* is the statement that this count is positive on the even numbers `≥ 4`.

This file contains:

* `spectralCount_pos_iff` : the (unconditional) transfer principle
  `0 < spectralCount n ↔ ∃ p q, p.Prime ∧ q.Prime ∧ p + q = n`;
* `goldbach_of_spectral_positivity` : the schema, i.e. spectral positivity on a range implies
  Goldbach's property on that range;
* `spectral_positivity_window` : the **discharge** of the spectral positivity hypothesis, proved
  unconditionally by a kernel-checked finite computation on the window `4 ≤ n ≤ 10000`;
* `goldbach_from_spectral_model` : the resulting unconditional theorem.

Goldbach's conjecture itself is open, so the unconditional discharge is necessarily restricted to
a finite window; the transfer principle `spectralCount_pos_iff` holds for *all* `n`.

The finite computation is carried out with a *sound* (but deliberately incomplete) Boolean
primality test `isPrimeB`, whose soundness is proved from `Nat.prime_def_le_sqrt`; only soundness
is needed, since the computation is used to *produce* prime witnesses.
-/

namespace Brockian
namespace GoldbachSchema

/-! ### The spectral model -/

/-- Spectral weight of the mode `p` for the number `n`: it is `1` exactly when `p` and `n - p`
are both prime and `p ≤ n`, i.e. when `p` contributes a Goldbach decomposition of `n`. -/

theorem goldbach_of_spectral_positivity (N : ℕ)
    (hspec : ∀ n : ℕ, 4 ≤ n → n ≤ N → Even n → 0 < spectralCount n) :
    ∀ n : ℕ, 4 ≤ n → n ≤ N → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n :=
  fun n h4 hN hev => (spectralCount_pos_iff n).mp (hspec n h4 hN hev)

/-! ### A kernel-friendly sound primality test -/

/-- `noFactorFrom n f d` performs at most `f` trial divisions of `n` by `d, d+1, …`.  It returns
`true` only when the loop terminates because `n < d * d`, i.e. only when it has genuinely
certified that `n` has no divisor `e` with `d ≤ e` and `e * e ≤ n`. -/
