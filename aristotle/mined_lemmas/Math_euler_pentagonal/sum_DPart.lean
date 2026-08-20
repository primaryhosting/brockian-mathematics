import Mathlib
import RequestProject.Pentagonal.GenFun

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
# Euler's pentagonal number theorem

`Math.euler_pentagonal` states that the generating function of the partition numbers
`p(n) = Fintype.card n.Partition` is the inverse of the pentagonal series
`∑_{k ∈ ℤ} (-1)^k q^{k(3k-1)/2}`, as formal power series over `ℤ`.

`Math.euler_pentagonal_prod` is the classical product form
`∏_{i ≥ 1} (1 - q^i) = ∑_{k ∈ ℤ} (-1)^k q^{k(3k-1)/2}`.
-/

open scoped PowerSeries.WithPiTopology

namespace Math

/-- **Euler's pentagonal number theorem** for the partition generating function:
`(∑_{n ≥ 0} p(n) q^n) * (∑_{k ∈ ℤ} (-1)^k q^{k(3k-1)/2}) = 1` in `ℤ⟦X⟧`.
Here the inner sum over `k ∈ Finset.Icc (-n) n` picks out the (at most one) integer `k`
with `n = k(3k-1)/2`, contributing `(-1)^k`. -/

theorem sum_DPart (n : ℕ) : ∑ S ∈ DPart n, (-1 : ℤ) ^ S.card = pentCoeff n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [DPart_zero, pentCoeff]
    decide
  · rw [← Finset.sum_filter_add_sum_filter_not (DPart n) Exceptional,
      sum_exceptional n hn, sum_nonExceptional n hn, add_zero]

end Pentagonal

import RequestProject.Pentagonal.Franklin

/-!
# The generating function form of Euler's pentagonal number theorem

Combining Franklin's involution (`Pentagonal.sum_DPart`) with Mathlib's generating function
machinery for partitions, we prove that the generating function of the partition numbers is
the inverse of `∑_{k ∈ ℤ} (-1)^k q^{k(3k-1)/2}`.
-/

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace Pentagonal

/-- The character selecting partitions into distinct parts, with the sign
`(-1)^(number of parts)`. -/
