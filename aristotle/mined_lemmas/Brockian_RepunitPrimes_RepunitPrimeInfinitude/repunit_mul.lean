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
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Brockian
namespace RepunitPrimes

/-- The `n`-th repunit `R n = 1 + 10 + ⋯ + 10 ^ (n - 1) = (10 ^ n - 1) / 9`,
i.e. the number written with `n` ones in base ten. -/

lemma repunit_mul (d k : ℕ) :
    repunit (d * k) = repunit d * ∑ i ∈ Finset.range k, (10 ^ d) ^ i := by
  set x : ℕ := 10 ^ d with hx
  set g : ℕ := ∑ i ∈ Finset.range k, x ^ i with hg
  have h1 : x * g + 1 = g + x ^ k := geom_sum_rec x k
  have h2 : 9 * repunit d + 1 = x := nine_mul_repunit_add_one d
  have h3 : 9 * repunit (d * k) + 1 = 10 ^ (d * k) := nine_mul_repunit_add_one (d * k)
  have h4 : (10 : ℕ) ^ (d * k) = x ^ k := by
    rw [hx, ← pow_mul]
  have h5 : 9 * (repunit d * g) + 1 = x ^ k := by
    have hxg : x * g = 9 * (repunit d * g) + g := by
      rw [← h2]; ring
    omega
  have h6 : 9 * repunit (d * k) + 1 = 9 * (repunit d * g) + 1 := by
    rw [h3, h4, h5]
  omega

/-- If `d ∣ n` then `R d ∣ R n`. -/
