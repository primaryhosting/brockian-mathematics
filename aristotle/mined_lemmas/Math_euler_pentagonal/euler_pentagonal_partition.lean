import Mathlib
import RequestProject.Pentagonal

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

`Math.euler_pentagonal` states the identity of formal power series over `ℤ`
$$\prod_{n = 1}^{\infty} (1 - X^n) = \sum_{k \in \mathbb Z} (-1)^k X^{k(3k-1)/2},$$
where the product and the sum are taken in the `X`-adic (product) topology on `ℤ⟦X⟧`.

`Math.euler_pentagonal_partition` states the corresponding statement for the generating
function of the partition function: the pentagonal series is the multiplicative inverse of
$\sum_{n} p(n) X^n$.

The combinatorial heart of the proof (Franklin's involution) is in
`RequestProject.Pentagonal`.
-/

namespace Math

open PowerSeries Finset Filter
open scoped PowerSeries.WithPiTopology

/-- The pentagonal exponent `k(3k-1)/2`. -/
abbrev pentExp : ℤ → ℕ := Franklin.pentExp

/-- The sign `(-1)^k`. -/
abbrev pentSign : ℤ → ℤ := Franklin.pentSign

/-- The pentagonal series `∑_{k ∈ ℤ} (-1)^k X^{k(3k-1)/2}` as a formal power series over `ℤ`. -/

theorem euler_pentagonal_partition : partitionSeries * pentagonalSeries = 1 := by
  have h1 := hasProd_partitionSeries
  have h2 := hasProd_one_sub_X_pow
  have h3 := h1.mul h2
  have hone : (fun i : ℕ => (∑' j : ℕ, (X : ℤ⟦X⟧) ^ ((i + 1) * j)) * (1 - X ^ (i + 1)))
      = fun _ : ℕ => (1 : ℤ⟦X⟧) := by
    funext i
    have hc : ((X : ℤ⟦X⟧) ^ (i + 1)).constantCoeff = 0 := by
      simp
    have := PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero hc
    simpa [pow_mul] using this
  rw [hone] at h3
  have h4 : partitionSeries * (PowerSeries.mk fun n => Franklin.pentCoeff n) = 1 :=
    (hasProd_one.unique h3).symm
  rw [pentagonalSeries_eq_mk]
  exact h4

end Math

import Mathlib

/-!
# Franklin's involution and the pentagonal number theorem (combinatorial core)

We represent a partition of `n` into distinct parts as a `Finset ℕ` of positive integers
summing to `n`.  The main result of this file is
`Franklin.sum_parts_eq_pentCoeff`:
`∑ S ∈ parts n, (-1) ^ #S = pentCoeff n`,
where `pentCoeff n` is the coefficient of `X ^ n` in `∑ k : ℤ, (-1)^k X^(k(3k-1)/2)`.
-/

open Finset

namespace Franklin

/-- The pentagonal exponent `k (3k-1) / 2` of an integer `k`. -/
