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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A *unitary divisor* of `n` is a divisor `d` with `gcd (d, n / d) = 1`, and `n` is *unitary
perfect* if the sum `σ*(n)` of its unitary divisors equals `2 n`.  Exactly five unitary
perfect numbers are known:

`6, 60, 90, 87360, 146361946186458562560000`,

and it is a long-standing open problem whether a sixth one exists.  Accordingly this file
does **not** prove unconditional existence; it develops the basic theory of `σ*`
(multiplicativity, values at prime powers), verifies that the five known numbers really are
unitary perfect, proves that every unitary perfect number is even, and finally proves the
target statement `SixthUnitaryPerfectExists` as a *conditional reduction*: any unitary
perfect number that either exceeds the largest known one or fails to be divisible by `3`
is a sixth unitary perfect number.

(The header comment above appears after the `import` line only because Lean requires
imports to come first in a file.)
-/

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd (d, n / d) = 1`. -/

lemma usigma_split_minFac {n : ℕ} (hn : 1 < n) :
    ∃ k m : ℕ, k ≠ 0 ∧ ¬ n.minFac ∣ m ∧ n = n.minFac ^ k * m ∧
      usigma n = (1 + n.minFac ^ k) * usigma m := by
  have hn0 : n ≠ 0 := by omega
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  obtain ⟨k, m, hpm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 n.minFac hp.ne_one
  have hk : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hnm
    exact hpm (hnm ▸ Nat.minFac_dvd n)
  refine ⟨k, m, hk, hpm, hnm, ?_⟩
  have hcop : Nat.Coprime (n.minFac ^ k) m :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)
  conv_lhs => rw [hnm]
  rw [usigma_mul_of_coprime hcop, usigma_prime_pow hp hk]

