import Mathlib

/-!
# Franklin's involution

Combinatorial core of Euler's pentagonal number theorem: the signed count of partitions of
`n` into distinct parts (sign `(-1)^(number of parts)`) is `0` unless `n` is a generalized
pentagonal number.

Partitions into distinct parts are encoded as finite sets of positive naturals.
-/

namespace EulerPentagonal

open Finset

/-- The largest element of `s` (junk value `0` for `s = ∅`). -/

theorem W_eq (n : ℕ) :
    W n = ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), if pentN k = n then (-1 : ℤ) ^ k.natAbs else 0 := by
  rw [W_eq_sum_exc, sum_exc_eq]

end EulerPentagonal

import Mathlib
import RequestProject.Franklin

/-!
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

open PowerSeries Finset EulerPentagonal
open scoped PowerSeries.WithPiTopology

namespace Math

/-- Expanding a finite product `∏ (1 - X^(i+1))` over all subsets. -/
