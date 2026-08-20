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

theorem coeff_genFun_sgnChar (n : ℕ) :
    (Nat.Partition.genFun sgnChar).coeff n = ∑ S ∈ DPart n, (-1 : ℤ) ^ S.card := by
  rw [Nat.Partition.coeff_genFun]
  refine (Finset.sum_of_injOn (toPartition n) ?_ (fun S _ => Finset.mem_univ _) ?_ ?_).symm
  · intro S hS T hT hST
    apply Finset.val_injective
    rw [← toPartition_parts (by simpa using hS), ← toPartition_parts (by simpa using hT), hST]
  · intro p _ hp
    by_contra hne
    have hnodup := nodup_of_prod_ne_zero hne
    exact hp ⟨p.parts.toFinset, Finset.mem_coe.mpr (toFinset_mem_DPart hnodup),
      toPartition_toFinset hnodup⟩
  · intro S hS
    rw [Finsupp.prod, Multiset.toFinsupp_support, toPartition_parts hS]
    have hval : Multiset.toFinset S.val = S := by ext x; simp
    rw [hval, Finset.prod_congr rfl (g := fun _ => (-1 : ℤ)) ?_, Finset.prod_const]
    intro x hx
    simp only [sgnChar, Multiset.toFinsupp_apply]
    rw [if_pos (Multiset.count_eq_one_of_mem S.nodup hx)]

