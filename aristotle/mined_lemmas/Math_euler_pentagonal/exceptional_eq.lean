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

theorem exceptional_eq {n : ℕ} {S : Finset ℕ} (hS : S ∈ DPart n) (hn : 1 ≤ n)
    (hexc : Exceptional S) :
    ∃ k : ℤ, k * (3 * k - 1) = 2 * (n : ℤ) ∧ -(n : ℤ) ≤ k ∧ k ≤ (n : ℤ) ∧ S = pentSet k := by
  obtain ⟨h0, hsum, hne, hm1, hmM, hr1, hrM⟩ := DPart_facts hS hn
  have hmem : mx S + 1 - runLen S ∈ S := runLen_subset (mem_Icc.mpr ⟨le_rfl, by omega⟩)
  have hmle := mn_le hmem
  rcases hexc with ⟨hA, hlt⟩ | ⟨hB, heq⟩
  · -- `S = {m, …, 2m-1}`
    have hkey : mx S + 1 - runLen S = mn S := by omega
    have hM2 : mx S + 1 = 2 * mn S := by omega
    have hSeq : S = Finset.Icc (mn S) (mx S) := by
      refine Finset.Subset.antisymm (fun x hx => mem_Icc.mpr ⟨mn_le hx, le_mx hx⟩) ?_
      intro x hx
      exact runLen_subset (by rw [hkey]; exact hx)
    have htn : ((mn S : ℤ)).toNat = mn S := Int.toNat_natCast _
    have hpent : S = pentSet (mn S : ℤ) := by
      rw [pentSet, if_pos (by omega), htn]
      conv_lhs => rw [hSeq]
      congr 1
      omega
    refine ⟨(mn S : ℤ), ?_, ?_, ?_, hpent⟩
    · have h := sum_pentSet_mul_two (mn S : ℤ)
      rw [← hpent, hsum] at h
      linarith
    · omega
    · have h := sum_pentSet_mul_two (mn S : ℤ)
      rw [← hpent, hsum] at h
      nlinarith [h, (by exact_mod_cast hm1 : (1 : ℤ) ≤ (mn S : ℤ))]
  · -- `S = {r+1, …, 2r}`
    have hSeq : S = Finset.Icc (runLen S + 1) (2 * runLen S) := by
      refine Finset.Subset.antisymm (fun x hx => ?_) ?_
      · have h1 := mn_le hx
        have h2 := le_mx hx
        exact mem_Icc.mpr ⟨by omega, by omega⟩
      · intro x hx
        simp only [mem_Icc] at hx
        exact runLen_subset (mem_Icc.mpr ⟨by omega, by omega⟩)
    have hna : (-(runLen S : ℤ)).natAbs = runLen S := by simp
    have hpent : S = pentSet (-(runLen S : ℤ)) := by
      rw [pentSet, if_neg (by omega), hna]
      exact hSeq
    refine ⟨-(runLen S : ℤ), ?_, ?_, ?_, hpent⟩
    · have h := sum_pentSet_mul_two (-(runLen S : ℤ))
      rw [← hpent, hsum] at h
      linarith
    · have h := sum_pentSet_mul_two (-(runLen S : ℤ))
      rw [← hpent, hsum] at h
      nlinarith [h, (by exact_mod_cast hr1 : (1 : ℤ) ≤ (runLen S : ℤ))]
    · omega

