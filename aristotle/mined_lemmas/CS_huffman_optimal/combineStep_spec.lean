import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem combineStep_spec (w : α → ℝ) (ts : List (HTree α)) (h : 2 ≤ ts.length) :
    ∃ (t1 t2 : HTree α) (rest : List (HTree α)),
      combineStep w ts = HTree.node t1 t2 :: rest ∧
      (↑ts : Multiset (HTree α)) = t1 ::ₘ t2 ::ₘ (↑rest : Multiset (HTree α)) ∧
      t1.wt w ≤ t2.wt w ∧ (∀ u ∈ rest, t2.wt w ≤ u.wt w) ∧
      rest.length + 2 = ts.length := by
  have hlen : (ts.mergeSort (treeLe w)).length = ts.length := List.length_mergeSort _
  have hperm : (ts.mergeSort (treeLe w)).Perm ts := List.mergeSort_perm _ _
  have hpw : List.Pairwise (fun a b => treeLe w a b = true) (ts.mergeSort (treeLe w)) :=
    List.pairwise_mergeSort (treeLe_trans w) (treeLe_total w) ts
  rcases hs : ts.mergeSort (treeLe w) with _ | ⟨t1, _ | ⟨t2, rest⟩⟩
  · rw [hs] at hlen; simp at hlen; omega
  · rw [hs] at hlen; simp at hlen; omega
  · refine ⟨t1, t2, rest, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [combineStep, hs]
    · have : (↑(ts.mergeSort (treeLe w)) : Multiset (HTree α)) = ↑ts :=
        Multiset.coe_eq_coe.2 hperm
      rw [hs] at this
      rw [← this]
      simp
    · rw [hs] at hpw
      have := (List.pairwise_cons.1 hpw).1 t2 (by simp)
      simpa [treeLe] using this
    · intro u hu
      rw [hs] at hpw
      have h2 := (List.pairwise_cons.1 (List.pairwise_cons.1 hpw).2).1 u hu
      simpa [treeLe] using h2
    · rw [hs] at hlen; simp at hlen; omega

