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

theorem sum_exceptional (n : ℕ) (hn : 1 ≤ n) :
    ∑ S ∈ (DPart n).filter Exceptional, (-1 : ℤ) ^ S.card = pentCoeff n := by
  rw [pentCoeff, ← Finset.sum_filter]
  refine (Finset.sum_bij (fun k _ => pentSet k) ?_ ?_ ?_ ?_).symm
  · intro k hk
    rw [Finset.mem_filter] at hk ⊢
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp only [zero_mul] at hk
      have := hk.2
      omega
    exact ⟨pentSet_mem_DPart hk.2, pentSet_exceptional hk0⟩
  · intro k hk l hl _
    rw [Finset.mem_filter] at hk hl
    exact pent_index_inj (by rw [hk.2, hl.2])
  · intro S hS
    rw [Finset.mem_filter] at hS
    obtain ⟨k, hk1, hk2, hk3, hk4⟩ := exceptional_eq hS.1 hn hS.2
    exact ⟨k, Finset.mem_filter.mpr ⟨mem_Icc.mpr ⟨hk2, hk3⟩, hk1⟩, hk4.symm⟩
  · intro k _
    rw [pentSet_card]

/-! ## The pentagonal number theorem -/

