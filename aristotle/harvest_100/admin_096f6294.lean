/-
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-- A comparison-based decision tree for sorting `5` elements.
A `node (a, b) l r` compares the input entries at positions `a` and `b`, continuing in `l`
if the comparison oracle answers `true` and in `r` otherwise; a `leaf p` outputs the
permutation `p`. -/
inductive DTree : Type
  | leaf : Equiv.Perm (Fin 5) → DTree
  | node : Fin 5 × Fin 5 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- Worst-case number of comparisons performed by the tree. -/
def depth : DTree → ℕ
  | leaf _ => 0
  | node _ l r => 1 + max (depth l) (depth r)

/-- Run the decision tree against a comparison oracle `o`, returning the permutation it outputs. -/
def run : DTree → (Fin 5 → Fin 5 → Bool) → Equiv.Perm (Fin 5)
  | leaf p, _ => p
  | node (a, b) l r, o => if o a b then run l o else run r o

/-- The (finite) set of permutations appearing as leaf labels of the tree. -/
def leaves : DTree → Finset (Equiv.Perm (Fin 5))
  | leaf p => {p}
  | node _ l r => leaves l ∪ leaves r

/-- A tree of depth `d` has at most `2 ^ d` distinct leaf labels. -/
theorem card_leaves_le_two_pow (t : DTree) : (leaves t).card ≤ 2 ^ depth t := by
  induction t with
  | leaf p => simp [leaves, depth]
  | node c l r ihl ihr =>
      have h : (leaves (node c l r)).card ≤ (leaves l).card + (leaves r).card := by
        simpa [leaves] using Finset.card_union_le (leaves l) (leaves r)
      refine h.trans ?_
      have hl : (leaves l).card ≤ 2 ^ max (depth l) (depth r) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : (leaves r).card ≤ 2 ^ max (depth l) (depth r) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      calc (leaves l).card + (leaves r).card
          ≤ 2 ^ max (depth l) (depth r) + 2 ^ max (depth l) (depth r) := Nat.add_le_add hl hr
        _ = 2 ^ depth (node c l r) := by
              have hd : depth (node c l r) = max (depth l) (depth r) + 1 := by
                simp [depth, Nat.add_comm]
              rw [hd, pow_succ]
              ring

/-- Every output of the tree is one of its leaf labels. -/
theorem run_mem_leaves (t : DTree) (o : Fin 5 → Fin 5 → Bool) : run t o ∈ leaves t := by
  induction t with
  | leaf p => simp [run, leaves]
  | node c l r ihl ihr =>
      obtain ⟨a, b⟩ := c
      by_cases h : o a b <;> simp [run, leaves, h, ihl, ihr]

/-- The comparison oracle induced by an input arrangement `p`: it reports whether the entry at
position `a` is at most the entry at position `b`. -/
def oracle (p : Equiv.Perm (Fin 5)) : Fin 5 → Fin 5 → Bool := fun a b => decide (p a ≤ p b)

/-- A tree *sorts* if, for every input arrangement, it outputs that arrangement (equivalently,
it correctly identifies the input's order, which is what a comparison sort must do). -/
def Sorts (t : DTree) : Prop := ∀ p : Equiv.Perm (Fin 5), run t (oracle p) = p

end DTree

open DTree

/-- **Comparison-sorting lower bound for 5 elements.**
Any comparison-based sorting algorithm on `5` elements (modelled as a decision tree that must
distinguish all `5!` input arrangements) performs at least `⌈log₂(5!)⌉ = 7` comparisons in the
worst case. -/
theorem sorting_lb_5 (t : DTree) (ht : Sorts t) :
    Nat.clog 2 (Nat.factorial 5) ≤ depth t := by
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 5))) ⊆ leaves t := by
    intro p _
    have := run_mem_leaves t (oracle p)
    rwa [ht p] at this
  have hcard : Nat.factorial 5 ≤ (leaves t).card := by
    have h1 : (Finset.univ : Finset (Equiv.Perm (Fin 5))).card ≤ (leaves t).card :=
      Finset.card_le_card huniv
    have h2 : (Finset.univ : Finset (Equiv.Perm (Fin 5))).card = Nat.factorial 5 := by
      simp [Finset.card_univ, Fintype.card_perm]
    omega
  have hle : Nat.factorial 5 ≤ 2 ^ depth t := hcard.trans (card_leaves_le_two_pow t)
  exact (Nat.clog_le_iff_le_pow (by norm_num)).2 hle

/-- `⌈log₂(5!)⌉ = 7`, so the bound above says: at least `7` comparisons. -/
theorem clog_factorial_five : Nat.clog 2 (Nat.factorial 5) = 7 := by decide

/-- Restatement of the lower bound with the explicit constant `7`. -/
theorem sorting_lb_5' (t : DTree) (ht : Sorts t) : 7 ≤ depth t := by
  have := sorting_lb_5 t ht
  rwa [clog_factorial_five] at this

/-! ### The hypothesis is satisfiable

To see that the bound above is not vacuous we exhibit a (wasteful, depth `25`) comparison tree
that does sort, namely the tree that queries every pair of positions in turn and then reads off
the unique arrangement consistent with the answers. -/

namespace DTree

/-- All ordered pairs of positions. -/
def allPairs : List (Fin 5 × Fin 5) :=
  (List.finRange 5).flatMap fun a => (List.finRange 5).map fun b => (a, b)

/-- The tree that queries the comparisons in `pairs` one after another, keeping track of the
list `cands` of arrangements still consistent with the answers received so far. -/
def build : List (Fin 5 × Fin 5) → List (Equiv.Perm (Fin 5)) → DTree
  | [], cands => leaf (cands.headD 1)
  | (a, b) :: rest, cands =>
      node (a, b) (build rest (cands.filter fun q => oracle q a b))
        (build rest (cands.filter fun q => !oracle q a b))

set_option maxRecDepth 100000 in
/-- An arrangement is determined by the answers to all comparisons. -/
theorem oracle_injective {q p : Equiv.Perm (Fin 5)} (h : ∀ a b, oracle q a b = oracle p a b) :
    q = p := by
  have key : ∀ e : Equiv.Perm (Fin 5),
      (∀ x y : Fin 5, decide (e x ≤ e y) = decide (x ≤ y)) → e = 1 := by
    decide
  have he : (q * p⁻¹ : Equiv.Perm (Fin 5)) = 1 := by
    refine key _ fun x y => ?_
    have := h (p⁻¹ x) (p⁻¹ y)
    simpa [oracle, Equiv.Perm.mul_apply] using this
  have := congrArg (fun e : Equiv.Perm (Fin 5) => e * p) he
  simpa [mul_assoc] using this

/-- Correctness of `build`: if the true arrangement `p` is among the candidates and the queried
comparisons suffice to single it out, the tree outputs `p`. -/
theorem run_build (pairs : List (Fin 5 × Fin 5)) :
    ∀ (cands : List (Equiv.Perm (Fin 5))) (p : Equiv.Perm (Fin 5)), p ∈ cands →
      (∀ q ∈ cands, (∀ ab ∈ pairs, oracle q ab.1 ab.2 = oracle p ab.1 ab.2) → q = p) →
      run (build pairs cands) (oracle p) = p := by
  induction pairs with
  | nil =>
      intro cands p hp hsep
      cases cands with
      | nil => simp at hp
      | cons c cs =>
          have : c = p := hsep c (by simp) (by simp)
          simp [build, run, this]
  | cons ab rest ih =>
      intro cands p hp hsep
      obtain ⟨a, b⟩ := ab
      by_cases hb : oracle p a b
      · have hmem : p ∈ cands.filter fun q => oracle q a b := by
          simp [List.mem_filter, hp, hb]
        have hsep' : ∀ q ∈ cands.filter fun q => oracle q a b,
            (∀ cd ∈ rest, oracle q cd.1 cd.2 = oracle p cd.1 cd.2) → q = p := by
          intro q hq hrest
          rw [List.mem_filter] at hq
          refine hsep q hq.1 ?_
          intro cd hcd
          rcases List.mem_cons.1 hcd with h | h
          · subst h; simp at hq ⊢; simp [hq.2, hb]
          · exact hrest cd h
        simpa [build, run, hb] using ih _ p hmem hsep'
      · have hb' : oracle p a b = false := by simpa using hb
        have hmem : p ∈ cands.filter fun q => !oracle q a b := by
          simp [List.mem_filter, hp, hb']
        have hsep' : ∀ q ∈ cands.filter fun q => !oracle q a b,
            (∀ cd ∈ rest, oracle q cd.1 cd.2 = oracle p cd.1 cd.2) → q = p := by
          intro q hq hrest
          rw [List.mem_filter] at hq
          refine hsep q hq.1 ?_
          intro cd hcd
          rcases List.mem_cons.1 hcd with h | h
          · subst h; simp at hq ⊢; simp [hq.2, hb']
          · exact hrest cd h
        simpa [build, run, hb'] using ih _ p hmem hsep'

theorem mem_allPairs (a b : Fin 5) : (a, b) ∈ allPairs := by
  simp [allPairs, List.mem_flatMap]

/-- The explicit sorting tree. -/
noncomputable def fullTree : DTree := build allPairs (Finset.univ : Finset (Equiv.Perm (Fin 5))).toList

theorem fullTree_sorts : Sorts fullTree := by
  intro p
  refine run_build allPairs _ p (by simp) ?_
  intro q _ hq
  exact oracle_injective fun a b => hq (a, b) (mem_allPairs a b)

end DTree

/-- The hypothesis of `sorting_lb_5` is satisfiable: comparison sorts of `5` elements exist. -/
theorem exists_sorting_tree : ∃ t : DTree, Sorts t :=
  ⟨DTree.fullTree, DTree.fullTree_sorts⟩

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

