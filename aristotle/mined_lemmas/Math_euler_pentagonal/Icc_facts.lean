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

theorem Icc_facts {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    mn (Finset.Icc a b) = a ∧ mx (Finset.Icc a b) = b ∧
      runLen (Finset.Icc a b) = b + 1 - a := by
  have hmn : mn (Finset.Icc a b) = a := by
    refine mn_eq (mem_Icc.mpr ⟨le_rfl, hab⟩) fun x hx => (mem_Icc.mp hx).1
  have hmx : mx (Finset.Icc a b) = b := by
    refine mx_eq (mem_Icc.mpr ⟨hab, le_rfl⟩) fun x hx => (mem_Icc.mp hx).2
  refine ⟨hmn, hmx, runLen_eq (by omega) ?_ ?_⟩
  · intro x hx
    rw [hmx] at hx
    simp only [mem_Icc] at hx ⊢
    omega
  · rw [hmx]
    simp only [mem_Icc]
    omega

