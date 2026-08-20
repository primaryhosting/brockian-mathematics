/-
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace CS

/-- An *input* to a comparison sort of three elements is described by the permutation
`σ : Equiv.Perm (Fin 3)` sending each position `i` to the rank of the element stored there. -/
abbrev Input : Type := Equiv.Perm (Fin 3)

/-- The outcome of comparing the elements stored at positions `i` and `j`
of the input described by `σ`: `true` means "the element at `i` is at most the one at `j`". -/
def ans (σ : Input) (i j : Fin 3) : Bool := decide (σ i ≤ σ j)

/-- A comparison-sorting algorithm on three elements, presented as a binary decision tree:
each internal node performs one comparison of two positions and branches on the outcome,
each leaf outputs a permutation (the claimed ordering of the input). -/
inductive DTree : Type
  | leaf : Input → DTree
  | node : Fin 3 → Fin 3 → DTree → DTree → DTree

/-- The output produced by the algorithm `t` on the input `σ`. -/
def run : DTree → Input → Input
  | .leaf a, _ => a
  | .node i j l r, σ => if ans σ i j then run l σ else run r σ

/-- The number of comparisons performed by the algorithm `t` on the input `σ`. -/
def cost : DTree → Input → ℕ
  | .leaf _, _ => 0
  | .node i j l r, σ => 1 + (if ans σ i j then cost l σ else cost r σ)

/-- Counting bound: if an algorithm distinguishes all the inputs of a set `S`
(i.e. gives them pairwise different outputs) using at most `d` comparisons on each of them,
then `S` has at most `2 ^ d` elements. -/
lemma card_le_two_pow_of_cost_le :
    ∀ (t : DTree) (d : ℕ) (S : Finset Input),
      (∀ σ ∈ S, cost t σ ≤ d) → Set.InjOn (run t) (S : Set Input) → S.card ≤ 2 ^ d := by
  intro t
  induction t with
  | leaf a =>
      intro d S _ hinj
      have h1 : S.card ≤ 1 := by
        refine Finset.card_le_one.mpr ?_
        intro x hx y hy
        exact hinj hx hy rfl
      exact h1.trans (Nat.one_le_two_pow)
  | node i j l r ihl ihr =>
      intro d S hcost hinj
      cases d with
      | zero =>
          have hS : S = ∅ := by
            refine Finset.eq_empty_of_forall_notMem ?_
            intro σ hσ
            have h := hcost σ hσ
            rw [cost] at h
            omega
          simp [hS]
      | succ k =>
          set S0 : Finset Input := S.filter (fun σ => ans σ i j = true) with hS0
          set S1 : Finset Input := S.filter (fun σ => ¬ (ans σ i j = true)) with hS1
          have hl : S0.card ≤ 2 ^ k := by
            refine ihl k S0 ?_ ?_
            · intro σ hσ
              rw [hS0, Finset.mem_filter] at hσ
              have h := hcost σ hσ.1
              rw [cost, if_pos hσ.2] at h
              omega
            · intro x hx y hy hxy
              have hx' : x ∈ S0 := hx
              have hy' : y ∈ S0 := hy
              rw [hS0, Finset.mem_filter] at hx' hy'
              refine hinj hx'.1 hy'.1 ?_
              rw [run, if_pos hx'.2, run, if_pos hy'.2]
              exact hxy
          have hr : S1.card ≤ 2 ^ k := by
            refine ihr k S1 ?_ ?_
            · intro σ hσ
              rw [hS1, Finset.mem_filter] at hσ
              have h := hcost σ hσ.1
              rw [cost, if_neg hσ.2] at h
              omega
            · intro x hx y hy hxy
              have hx' : x ∈ S1 := hx
              have hy' : y ∈ S1 := hy
              rw [hS1, Finset.mem_filter] at hx' hy'
              refine hinj hx'.1 hy'.1 ?_
              rw [run, if_neg hx'.2, run, if_neg hy'.2]
              exact hxy
          have hsplit : S0.card + S1.card = S.card := by
            rw [hS0, hS1]
            exact Finset.card_filter_add_card_filter_not _
          have : S.card ≤ 2 ^ k + 2 ^ k := by omega
          calc S.card ≤ 2 ^ k + 2 ^ k := this
            _ = 2 ^ (k + 1) := by ring

/-- **Comparison-sorting lower bound for three elements.**

Any comparison sort of `3` elements, modelled as a binary decision tree whose internal nodes
compare two positions and whose leaves output the claimed ordering, needs at least
`⌈log₂ (3!)⌉ = 3` comparisons in the worst case: if the algorithm `t` is correct on every input,
then there is an input on which it performs at least `Nat.clog 2 (3!)` comparisons. -/
theorem sorting_lb_3 (t : DTree) (hcorrect : ∀ σ : Input, run t σ = σ) :
    ∃ σ : Input, Nat.clog 2 (Nat.factorial 3) ≤ cost t σ := by
  have hclog : Nat.clog 2 (Nat.factorial 3) = 3 := by norm_num [Nat.factorial, Nat.clog]
  by_contra hcon
  push_neg at hcon
  simp only [hclog] at hcon
  have hb : ∀ σ ∈ (Finset.univ : Finset Input), cost t σ ≤ 2 := by
    intro σ _
    have := hcon σ
    omega
  have hinj : Set.InjOn (run t) ((Finset.univ : Finset Input) : Set Input) := by
    intro x _ y _ hxy
    rwa [hcorrect x, hcorrect y] at hxy
  have hle := card_le_two_pow_of_cost_le t 2 Finset.univ hb hinj
  have hcard : (Finset.univ : Finset Input).card = 6 := by
    simp [Finset.card_univ, Fintype.card_perm, Nat.factorial]
  rw [hcard] at hle
  norm_num at hle

/-- An explicit comparison sort of three elements using at most three comparisons
(compare positions `0,1`, then the remaining pairs). -/
def sorter3 : DTree :=
  .node 0 1
    (.node 1 2
      (.leaf 1)
      (.node 0 2
        (.leaf (Equiv.swap 1 2))
        (.leaf (Equiv.swap 0 1 * Equiv.swap 1 2))))
    (.node 0 2
      (.leaf (Equiv.swap 0 1))
      (.node 1 2
        (.leaf (Equiv.swap 1 2 * Equiv.swap 0 1))
        (.leaf (Equiv.swap 0 2))))

/-- The lower bound of `⌈log₂ (3!)⌉ = 3` comparisons is attained: `sorter3` is a correct
comparison sort of three elements never using more than `⌈log₂ (3!)⌉` comparisons.
In particular the hypothesis of `CS.sorting_lb_3` is satisfiable. -/
theorem sorter3_correct_and_optimal :
    (∀ σ : Input, run sorter3 σ = σ) ∧
      ∀ σ : Input, cost sorter3 σ ≤ Nat.clog 2 (Nat.factorial 3) := by
  have hclog : Nat.clog 2 (Nat.factorial 3) = 3 := by norm_num [Nat.factorial, Nat.clog]
  rw [hclog]
  exact ⟨by decide, by decide⟩

end CS

