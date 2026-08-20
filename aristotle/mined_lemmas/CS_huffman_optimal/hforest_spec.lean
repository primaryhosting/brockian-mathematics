import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma hforest_spec (w : ι → ℝ) :
    ∀ (F : List (ℝ × HTree ι)) (T : HTree ι), hforest F = some T →
      (∀ p ∈ F, p.1 = HTree.wsum w p.2) →
      (T.elems.Perm (F.flatMap (fun p => p.2.elems))) ∧
        HTree.tcost w T
          = (F.map (fun p => HTree.tcost w p.2)).sum + hcost (F.map Prod.fst) := by
  intro F
  induction F using hforest.induct with
  | case1 =>
      intro T hT _
      rw [hforest] at hT
      exact absurd hT (by simp)
  | case2 a t =>
      intro T hT _
      rw [hforest] at hT
      have : T = t := by simpa using hT.symm
      subst this
      constructor
      · simp
      · simp
  | case3 a s b t rest ih =>
      intro T hT hw
      rw [hforest] at hT
      set x : ℝ × HTree ι := (a + b, HTree.node s t) with hx
      set F' : List (ℝ × HTree ι) :=
        List.orderedInsert (fun p q : ℝ × HTree ι => p.1 ≤ q.1) x rest with hF'
      have hperm : F'.Perm (x :: rest) :=
        List.perm_orderedInsert (fun p q : ℝ × HTree ι => p.1 ≤ q.1) x rest
      have has : a = HTree.wsum w s := hw (a, s) (by simp)
      have hbt : b = HTree.wsum w t := hw (b, t) (by simp)
      have hw' : ∀ p ∈ F', p.1 = HTree.wsum w p.2 := by
        intro p hp
        have : p ∈ x :: rest := hperm.mem_iff.mp hp
        rcases List.mem_cons.mp this with h | h
        · subst h; simp [hx, has, hbt]
        · exact hw p (by simp [h])
      obtain ⟨hE, hC⟩ := ih T hT hw'
      have hflat : (F'.flatMap (fun p => p.2.elems)).Perm
          (((a, s) :: (b, t) :: rest).flatMap (fun p => p.2.elems)) := by
        refine (hperm.flatMap_right _).trans ?_
        simp [hx, List.flatMap_cons, List.append_assoc]
      refine ⟨hE.trans hflat, ?_⟩
      have hsum : (F'.map (fun p => HTree.tcost w p.2)).sum
          = HTree.tcost w (HTree.node s t) + (rest.map (fun p => HTree.tcost w p.2)).sum := by
        have := (hperm.map (fun p => HTree.tcost w p.2)).sum_eq
        simpa [hx] using this
      have hmapfst : F'.map Prod.fst = List.orderedInsert (· ≤ ·) (a + b) (rest.map Prod.fst) := by
        simpa [hx] using map_fst_orderedInsert x rest
      rw [hC, hsum, hmapfst]
      simp only [List.map_cons, List.sum_cons, hcost_cons_cons, HTree.tcost_node]
      rw [← has, ← hbt]
      ring

end CS

import RequestProject.Huffman

namespace CS
/-!
# Sanity checks

Small worked examples confirming that the definitions compute the intended quantities:
for the weights `1, 2, 3` Huffman coding gives codeword lengths `2, 2, 1`, i.e. an
expected length of `1*2 + 2*2 + 3*1 = 9`.
-/
example : hcost [1, 2, 3] = 9 := by
  rw [hcost_cons_cons]
  norm_num [List.orderedInsert, hcost_cons_cons]

example : Hmul ({1, 2, 3} : Multiset ℝ) = 9 := by
  have : ({1, 2, 3} : Multiset ℝ).sort (· ≤ ·) = [1, 2, 3] := by
    refine sort_coe_of_sorted (by norm_num)
  rw [Hmul, this, hcost_cons_cons]
  norm_num [List.orderedInsert, hcost_cons_cons]

example (w : Fin 3 → ℝ) (h0 : w 0 = 1) (h1 : w 1 = 2) (h2 : w 2 = 3) :
    expLength w (huffmanCode w) = 9 := by
  rw [huffmanCode_expLength]
  have hm : (Finset.univ.val.map w : Multiset ℝ) = {w 0, w 1, w 2} := rfl
  rw [hm, h0, h1, h2]
  have : ({1, 2, 3} : Multiset ℝ).sort (· ≤ ·) = [1, 2, 3] := by
    refine sort_coe_of_sorted (by norm_num)
  rw [Hmul, this, hcost_cons_cons]
  norm_num [List.orderedInsert, hcost_cons_cons]

end CS

import RequestProject.Lower
import RequestProject.Kraft

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

instance instIsTransWle : IsTrans (ℝ × HTree ι) (fun p q => p.1 ≤ q.1) :=
  ⟨fun _ _ _ h1 h2 => le_trans h1 h2⟩

instance instTotalWle : Std.Total (fun p q : ℝ × HTree ι => p.1 ≤ q.1) :=
  ⟨fun a b => le_total a.1 b.1⟩

/-- A code is a *prefix code* if no codeword is a prefix of the codeword of another
symbol. -/
