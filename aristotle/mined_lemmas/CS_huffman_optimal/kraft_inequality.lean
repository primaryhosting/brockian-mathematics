import RequestProject.HuffmanKraft

/-!
# Weighted depth multisets, the Huffman merging process, and the optimality bound
-/

namespace CS

/-- A *weighted depth multiset*: a finite multiset of pairs `(weight, codeword length)`. -/
abbrev WD := Multiset (ℝ × ℕ)

/-- The expected codeword length associated to a weighted depth multiset. -/

theorem kraft_inequality (cs : List (List Bool)) (h : PrefixFree cs) :
    (cs.map fun u => (1 / 2 : ℝ) ^ u.length).sum ≤ 1 := by
  classical
  obtain ⟨M, hM⟩ : ∃ M, ∀ u ∈ cs, u.length ≤ M := by
    induction cs with
    | nil => exact ⟨0, by simp⟩
    | cons a l ih =>
      obtain ⟨M, hM⟩ := ih h.of_cons
      exact ⟨max M a.length, by
        intro u hu
        rcases List.mem_cons.1 hu with rfl | hu
        · exact le_max_right _ _
        · exact le_trans (hM u hu) (le_max_left _ _)⟩
  have hnd : cs.Nodup := h.nodup
  have hpair := h.forall PrefixFree.symm
  -- the extension sets are pairwise disjoint
  have hdisj : (cs.toFinset : Set (List Bool)).PairwiseDisjoint (exts M) := by
    intro u hu v hv huv
    simp only [Finset.mem_coe, List.mem_toFinset] at hu hv
    rw [Function.onFun, Finset.disjoint_left]
    rintro x hx hx'
    simp only [exts, Finset.mem_filter] at hx hx'
    rcases List.prefix_or_prefix_of_prefix hx.2 hx'.2 with hc | hc
    · exact (hpair hu hv huv).1 hc
    · exact (hpair hu hv huv).2 hc
  have hcard : ∑ u ∈ cs.toFinset, (exts M u).card ≤ 2 ^ M := by
    rw [← Finset.card_biUnion hdisj]
    calc (cs.toFinset.biUnion (exts M)).card ≤ (allLists M).card :=
          Finset.card_le_card (by
            intro x hx
            simp only [Finset.mem_biUnion] at hx
            obtain ⟨u, _, hu⟩ := hx
            exact (Finset.mem_filter.1 hu).1)
      _ = 2 ^ M := card_allLists M
  have key : ∀ u ∈ cs.toFinset, (1 / 2 : ℝ) ^ u.length = ((exts M u).card : ℝ) / 2 ^ M := by
    intro u hu
    rw [List.mem_toFinset] at hu
    have hle := hM u hu
    have hsplit : (2 : ℝ) ^ M = 2 ^ (M - u.length) * 2 ^ u.length := by
      rw [← pow_add]; congr 1; omega
    rw [card_exts hle]
    push_cast
    rw [hsplit, eq_div_iff (by positivity), mul_comm ((2:ℝ) ^ (M - u.length)),
      ← mul_assoc, ← mul_pow]
    norm_num
  rw [← List.sum_toFinset _ hnd, Finset.sum_congr rfl key, ← Finset.sum_div,
    div_le_one (by positivity)]
  calc (∑ u ∈ cs.toFinset, ((exts M u).card : ℝ))
      = ((∑ u ∈ cs.toFinset, (exts M u).card : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((2 ^ M : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = 2 ^ M := by push_cast; ring

end CS

import Mathlib

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

