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

theorem pentExp_spec (k : ℤ) : 2 * (pentExp k : ℤ) = k * (3 * k - 1) := by
  have heven : (2 : ℤ) ∣ k * (3 * k - 1) := by
    rcases Int.even_or_odd k with h | h
    · obtain ⟨m, rfl⟩ := h; exact ⟨m * (3 * (m + m) - 1), by ring⟩
    · obtain ⟨m, rfl⟩ := h; exact ⟨(2 * m + 1) * (3 * m + 1), by ring⟩
  have hnonneg : 0 ≤ k * (3 * k - 1) := by nlinarith [sq_nonneg k, sq_nonneg (k - 1)]
  rw [pentExp, Int.toNat_of_nonneg (Int.ediv_nonneg hnonneg (by norm_num))]
  exact Int.mul_ediv_cancel' heven

