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

theorem euler_pentagonal_prod :
    HasProd (fun i : ℕ => 1 - (PowerSeries.X : PowerSeries ℤ) ^ (i + 1))
      (PowerSeries.mk fun n : ℕ => ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
        if k * (3 * k - 1) = 2 * (n : ℤ) then (-1 : ℤ) ^ k.natAbs else 0) :=
  Pentagonal.genFun_sgnChar_eq ▸ Pentagonal.hasProd_sgnChar

end Math

import Mathlib

/-!
# Franklin's involution and the pentagonal number theorem (combinatorial core)

We work with partitions of `n` into distinct positive parts, encoded as `Finset ℕ` not
containing `0` and with sum `n`.  The main result of this file is

`Pentagonal.sum_DPart : ∑ S ∈ DPart n, (-1) ^ S.card = pentCoeff n`

where `pentCoeff n` is `(-1)^k` if `n = k(3k-1)/2` for some `k : ℤ`, and `0` otherwise.
-/

open Finset

namespace Pentagonal

/-! ## Basic quantities attached to a finite set of positive integers -/

/-- The smallest element of `S` (junk value `0` if `S` is empty). -/
