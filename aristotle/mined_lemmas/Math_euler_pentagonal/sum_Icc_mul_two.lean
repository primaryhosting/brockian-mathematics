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

theorem sum_Icc_mul_two (a b : ℕ) (h : a ≤ b + 1) :
    (∑ i ∈ Finset.Icc a b, i) * 2 + a * (a - 1) = (b + 1) * b := by
  have h1 : Finset.Icc a b = Finset.Ico a (b + 1) := (Finset.Ico_add_one_right_eq_Icc a b).symm
  have h2 : ∑ i ∈ Finset.Ico 0 a, i + ∑ i ∈ Finset.Ico a (b + 1), i =
      ∑ i ∈ Finset.Ico 0 (b + 1), i := Finset.sum_Ico_consecutive _ (Nat.zero_le a) h
  rw [← Finset.range_eq_Ico] at h2
  have h3 := Finset.sum_range_id_mul_two a
  have h4 := Finset.sum_range_id_mul_two (b + 1)
  simp only [Nat.add_sub_cancel] at h4
  rw [h1]
  have h5 : (∑ i ∈ Finset.range a, i + ∑ i ∈ Finset.Ico a (b + 1), i) * 2 =
      (∑ i ∈ Finset.range (b + 1), i) * 2 := by rw [h2]
  rw [add_mul, h3, h4] at h5
  linarith

