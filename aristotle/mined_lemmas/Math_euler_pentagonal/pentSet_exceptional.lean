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

theorem pentSet_exceptional {k : ℤ} (hk : k ≠ 0) : Exceptional (pentSet k) := by
  rcases lt_or_ge 0 k with hpos | hneg
  · obtain ⟨c, hc⟩ : ∃ c, k.toNat = c + 1 := ⟨k.toNat - 1, by omega⟩
    have he : 2 * k.toNat - 1 = 2 * c + 1 := by omega
    rw [pentSet, if_pos hpos, he, hc]
    obtain ⟨h1, h2, h3⟩ := Icc_facts (a := c + 1) (b := 2 * c + 1) (by omega) (by omega)
    exact Or.inl ⟨by omega, by omega⟩
  · have hj : 1 ≤ k.natAbs := by omega
    rw [pentSet, if_neg (by omega)]
    obtain ⟨h1, h2, h3⟩ := Icc_facts (a := k.natAbs + 1) (b := 2 * k.natAbs) (by omega) (by omega)
    exact Or.inr ⟨by omega, by omega⟩

