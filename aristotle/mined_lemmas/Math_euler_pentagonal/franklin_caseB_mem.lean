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

theorem franklin_caseB_mem (hS : S ∈ DPart n) (hn : 1 ≤ n) (hB : runLen S < mn S)
    (hM : mx S ≠ 2 * runLen S) : franklin S ∈ DPart n := by
  obtain ⟨h0, hsum, hne, hm1, hmM, hr1, hrM⟩ := DPart_facts hS hn
  have h2r := caseB_two_mul_lt hS hn hB hM
  have hnot : mx S - runLen S ∉ S := notMem_mx_sub_runLen h0
  rw [mem_DPart]
  constructor
  · intro hmem
    rcases (mem_franklin_caseB hS hn hB hM 0).mp hmem with h | ⟨h, -⟩ | ⟨h, -⟩
    · omega
    · exact h0 h
    · omega
  · rw [franklin, if_neg (not_le.mpr hB),
      Finset.sum_insert (franklin_caseB_notMem hS hn hB hM)]
    have hnot' : mx S + 1 - runLen S - 1 ∉ S := by
      have he : mx S + 1 - runLen S - 1 = mx S - runLen S := by omega
      rw [he]; exact hnot
    have hd : (∑ x ∈ S.image (dn (mx S + 1 - runLen S)), x) +
        (S.filter (fun x => mx S + 1 - runLen S ≤ x)).card = ∑ x ∈ S, x :=
      sum_image_dn hnot'
    rw [filter_ge_eq_Icc (le_refl (runLen S)), Nat.card_Icc] at hd
    omega

