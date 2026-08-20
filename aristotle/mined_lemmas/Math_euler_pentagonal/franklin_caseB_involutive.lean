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

theorem franklin_caseB_involutive (hS : S ∈ DPart n) (hn : 1 ≤ n) (hB : runLen S < mn S)
    (hM : mx S ≠ 2 * runLen S) : franklin (franklin S) = S := by
  obtain ⟨h0, hsum, hne, hm1, hmM, hr1, hrM⟩ := DPart_facts hS hn
  have h2r := caseB_two_mul_lt hS hn hB hM
  have hmxT := franklin_caseB_mx hS hn hB hM
  have hmnT := franklin_caseB_mn hS hn hB hM
  have hle := franklin_caseB_le_runLen hS hn hB hM
  have hnot : mx S - runLen S ∉ S := notMem_mx_sub_runLen h0
  rw [franklin, if_pos hle, hmnT, hmxT]
  ext x
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
    rcases (mem_franklin_caseB hS hn hB hM y).mp hy2 with rfl | ⟨hz1, hz2⟩ | ⟨hz1, hz2⟩
    · exact absurd rfl hy1
    · rwa [up, if_neg (by omega)]
    · rw [up, if_pos (by omega)]
      exact runLen_subset (mem_Icc.mpr ⟨by omega, by omega⟩)
  · intro hx
    have hxm := mn_le hx
    have hxM := le_mx hx
    have hxne : x ≠ mx S - runLen S := fun e => hnot (e ▸ hx)
    by_cases hlow : x + runLen S < mx S
    · refine ⟨x, ⟨by omega, (mem_franklin_caseB hS hn hB hM x).mpr (Or.inr (Or.inl ⟨hx, hlow⟩))⟩,
        ?_⟩
      rw [up, if_neg (by omega)]
    · refine ⟨x - 1, ⟨by omega, (mem_franklin_caseB hS hn hB hM (x - 1)).mpr
        (Or.inr (Or.inr ⟨by omega, by omega⟩))⟩, ?_⟩
      rw [up, if_pos (by omega)]
      omega

end CaseB

/-! ## The involution -/

/-- On a non-exceptional set, exactly one of the two cases of Franklin's map applies. -/
