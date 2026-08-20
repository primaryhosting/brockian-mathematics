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
