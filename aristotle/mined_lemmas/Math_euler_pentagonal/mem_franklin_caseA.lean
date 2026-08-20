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

theorem mem_franklin_caseA (h0 : 0 ∉ S) (hne : S.Nonempty) (hA : mn S ≤ runLen S)
    (hM : 2 * mn S ≤ mx S) (x : ℕ) :
    x ∈ franklin S ↔ ((x ∈ S ∧ x ≠ mn S ∧ x ≤ mx S - mn S) ∨
      (mx S + 2 - mn S ≤ x ∧ x ≤ mx S + 1)) := by
  have hm1 : 1 ≤ mn S := Nat.pos_of_ne_zero fun h => h0 (h ▸ mn_mem hne)
  have hsub : Finset.Icc (mx S + 1 - mn S) (mx S) ⊆ S := by
    intro y hy
    simp only [mem_Icc] at hy
    exact runLen_subset (mem_Icc.mpr ⟨by omega, hy.2⟩)
  rw [franklin, if_pos hA]
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
    have hyM : y ≤ mx S := le_mx hy2
    by_cases hy : mx S + 1 - mn S ≤ y
    · right
      simp only [up, if_pos hy]
      omega
    · left
      simp only [up, if_neg hy]
      exact ⟨hy2, hy1, by omega⟩
  · rintro (⟨hx1, hx2, hx3⟩ | ⟨hx1, hx2⟩)
    · refine ⟨x, ⟨hx2, hx1⟩, ?_⟩
      simp only [up, if_neg (by omega : ¬ (mx S + 1 - mn S ≤ x))]
    · refine ⟨x - 1, ⟨by omega, hsub (mem_Icc.mpr ⟨by omega, by omega⟩)⟩, ?_⟩
      simp only [up, if_pos (by omega : mx S + 1 - mn S ≤ x - 1)]
      omega

