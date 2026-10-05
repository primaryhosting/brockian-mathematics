/-
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- A comparison-based decision tree for sorting 4 elements.  An internal node
compares the input elements at two positions `i j : Fin 4` and branches on the
answer; a leaf reports an output of type `α`. -/
inductive CompTree (α : Type) where
  | leaf : α → CompTree α
  | node : Fin 4 → Fin 4 → CompTree α → CompTree α → CompTree α
  deriving Inhabited

namespace CompTree

variable {α : Type}

/-- Worst-case number of comparisons performed by the tree (its height). -/
def depth : CompTree α → ℕ
  | .leaf _ => 0
  | .node _ _ t f => 1 + max (depth t) (depth f)

/-- Running the tree on an input.  The input is described by the permutation
`σ : Equiv.Perm (Fin 4)` sending a position to the rank of the element stored
there; the comparison "is the element at position `i` smaller than the one at
position `j`?" is thus answered by `σ i < σ j`. -/
def run : CompTree α → Equiv.Perm (Fin 4) → α
  | .leaf a, _ => a
  | .node i j t f, σ => if σ i < σ j then run t σ else run f σ

/-- The (finite) set of possible outputs, i.e. the labels of the leaves. -/
def outputs [DecidableEq α] : CompTree α → Finset α
  | .leaf a => {a}
  | .node _ _ t f => outputs t ∪ outputs f

/-- Any run of the tree produces one of its leaf labels. -/
theorem run_mem_outputs [DecidableEq α] (t : CompTree α) (σ : Equiv.Perm (Fin 4)) :
    run t σ ∈ outputs t := by
  induction t with
  | leaf a => simp [run, outputs]
  | node i j tt tf iht ihf =>
      by_cases h : σ i < σ j <;> simp [run, outputs, h, iht, ihf]

/-- A binary decision tree of depth `d` has at most `2 ^ d` distinct outputs. -/
theorem card_outputs_le [DecidableEq α] (t : CompTree α) :
    (outputs t).card ≤ 2 ^ depth t := by
  induction t with
  | leaf a => simp [outputs, depth]
  | node i j tt tf iht ihf =>
      have h1 : (outputs (node i j tt tf)).card ≤ (outputs tt).card + (outputs tf).card := by
        simpa [outputs] using Finset.card_union_le (outputs tt) (outputs tf)
      have h2 : (2 : ℕ) ^ depth tt ≤ 2 ^ max (depth tt) (depth tf) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have h3 : (2 : ℕ) ^ depth tf ≤ 2 ^ max (depth tt) (depth tf) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have : (outputs (node i j tt tf)).card
          ≤ 2 ^ max (depth tt) (depth tf) + 2 ^ max (depth tt) (depth tf) :=
        h1.trans (Nat.add_le_add (iht.trans h2) (ihf.trans h3))
      simpa [depth, pow_succ, pow_add, two_mul, Nat.add_comm] using this

end CompTree

open CompTree

/-- **Comparison-sorting lower bound for 4 elements.**
If a comparison tree correctly sorts every input of 4 distinct elements — i.e. on
input described by the ranking permutation `σ` it outputs `σ` — then its
worst-case number of comparisons is at least `⌈log₂ (4!)⌉ = 5`. -/
theorem sorting_lb_4 (t : CompTree (Equiv.Perm (Fin 4)))
    (hcorrect : ∀ σ : Equiv.Perm (Fin 4), run t σ = σ) :
    Nat.clog 2 (Nat.factorial 4) ≤ depth t := by
  classical
  have hsub : (Finset.univ : Finset (Equiv.Perm (Fin 4))) ⊆ outputs t := by
    intro σ _
    have := run_mem_outputs t σ
    rwa [hcorrect σ] at this
  have hcard : (24 : ℕ) ≤ (outputs t).card := by
    have := Finset.card_le_card hsub
    simpa [Fintype.card_perm] using this
  have hpow : (24 : ℕ) ≤ 2 ^ depth t := hcard.trans (card_outputs_le t)
  have hclog : Nat.clog 2 24 ≤ Nat.clog 2 (2 ^ depth t) := Nat.clog_mono_right _ hpow
  rw [Nat.clog_pow _ _ (by norm_num)] at hclog
  have h24 : Nat.clog 2 (Nat.factorial 4) = 5 := by decide
  have h5 : Nat.clog 2 24 = 5 := by decide
  omega

/-- Concretely, the bound is 5 comparisons. -/
theorem sorting_lb_4' (t : CompTree (Equiv.Perm (Fin 4)))
    (hcorrect : ∀ σ : Equiv.Perm (Fin 4), run t σ = σ) :
    5 ≤ depth t := by
  have := sorting_lb_4 t hcorrect
  have h : Nat.clog 2 (Nat.factorial 4) = 5 := by decide
  omega

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

