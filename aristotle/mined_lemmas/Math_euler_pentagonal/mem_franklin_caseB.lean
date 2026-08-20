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

theorem mem_franklin_caseB (hS : S ∈ DPart n) (hn : 1 ≤ n) (hB : runLen S < mn S)
    (hM : mx S ≠ 2 * runLen S) (x : ℕ) :
    x ∈ franklin S ↔ (x = runLen S ∨ (x ∈ S ∧ x + runLen S < mx S) ∨
      (mx S - runLen S ≤ x ∧ x ≤ mx S - 1)) := by
  obtain ⟨h0, hsum, hne, hm1, hmM, hr1, hrM⟩ := DPart_facts hS hn
  have h2r := caseB_two_mul_lt hS hn hB hM
  have hnot : mx S - runLen S ∉ S := notMem_mx_sub_runLen h0
  rw [franklin, if_neg (not_le.mpr hB)]
  simp only [Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (rfl | ⟨y, hy, rfl⟩)
    · exact Or.inl rfl
    · have hyM := le_mx hy
      have hym := mn_le hy
      have hyne : y ≠ mx S - runLen S := fun e => hnot (e ▸ hy)
      by_cases hc : mx S + 1 - runLen S ≤ y
      · refine Or.inr (Or.inr ?_)
        rw [dn, if_pos hc]
        omega
      · refine Or.inr (Or.inl ?_)
        rw [dn, if_neg hc]
        exact ⟨hy, by omega⟩
  · rintro (rfl | ⟨hx, hx2⟩ | ⟨hx1, hx2⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨x, hx, by rw [dn, if_neg (by omega)]⟩
    · refine Or.inr ⟨x + 1, runLen_subset (mem_Icc.mpr ⟨by omega, by omega⟩), ?_⟩
      rw [dn, if_pos (by omega)]
      omega

