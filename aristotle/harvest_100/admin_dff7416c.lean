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

Any comparison sort of `4` elements needs at least `⌈log₂(4!)⌉ = 5` comparisons in the
worst case.

A comparison sort is modelled as a (binary) decision tree: an internal node compares two
input positions `i` and `j`, and branches on the answer; a leaf outputs a permutation
(the claimed sorted order).  An input is a permutation `σ` assigning to each position its
rank, and the comparison `i ≤ j` is answered by `σ i ≤ σ j`.  The tree *sorts* if on every
input it outputs the correct permutation.

The main result `CS.sorting_lb_4` states that any such tree for `4` elements has depth at
least `Nat.clog 2 (4!) = 5`.
-/

namespace CS

/-- A comparison-based decision tree on `n` elements: a leaf carries the output
permutation, an internal node compares positions `i` and `j`. -/
inductive DTree (n : ℕ) where
  | leaf : Equiv.Perm (Fin n) → DTree n
  | node : Fin n → Fin n → DTree n → DTree n → DTree n
  deriving Inhabited

namespace DTree

variable {n : ℕ}

/-- Worst-case number of comparisons performed by the tree. -/
def depth : DTree n → ℕ
  | leaf _ => 0
  | node _ _ t f => max (depth t) (depth f) + 1

/-- Running the tree on the input whose ranking is `σ`: the comparison of positions `i`
and `j` is answered by comparing the ranks `σ i` and `σ j`. -/
def run : DTree n → Equiv.Perm (Fin n) → Equiv.Perm (Fin n)
  | leaf p, _ => p
  | node i j t f, σ => if σ i ≤ σ j then run t σ else run f σ

/-- The list of outputs occurring at the leaves of the tree. -/
def leaves : DTree n → List (Equiv.Perm (Fin n))
  | leaf p => [p]
  | node _ _ t f => leaves t ++ leaves f

theorem run_mem_leaves (t : DTree n) (σ : Equiv.Perm (Fin n)) : run t σ ∈ leaves t := by
  induction t with
  | leaf p => simp [run, leaves]
  | node i j a b ha hb =>
      by_cases h : σ i ≤ σ j <;> simp [run, leaves, h, ha, hb]

theorem length_leaves_le (t : DTree n) : (leaves t).length ≤ 2 ^ depth t := by
  induction t with
  | leaf p => simp [leaves, depth]
  | node i j a b ha hb =>
      have h1 : (leaves a).length ≤ 2 ^ max (depth a) (depth b) :=
        ha.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have h2 : (leaves b).length ≤ 2 ^ max (depth a) (depth b) :=
        hb.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      simp only [leaves, depth, List.length_append, pow_succ]
      omega

end DTree

open DTree

/-- Sanity check: the model is not vacuous.  For two elements, one comparison sorts. -/
example : ∀ σ : Equiv.Perm (Fin 2),
    run (DTree.node 0 1 (DTree.leaf 1) (DTree.leaf (Equiv.swap 0 1))) σ = σ := by decide

/-- A sorting tree must have at least `n !` leaves. -/
theorem factorial_le_length_leaves {n : ℕ} (t : DTree n)
    (hsort : ∀ σ : Equiv.Perm (Fin n), run t σ = σ) :
    Nat.factorial n ≤ (leaves t).length := by
  classical
  have hsub : (Finset.univ : Finset (Equiv.Perm (Fin n))) ⊆ (leaves t).toFinset := by
    intro σ _
    have hmem := run_mem_leaves t σ
    rw [hsort σ] at hmem
    simpa using hmem
  have h1 : Nat.factorial n ≤ (leaves t).toFinset.card := by
    have := Finset.card_le_card hsub
    simpa [Fintype.card_perm] using this
  exact h1.trans (List.toFinset_card_le _)

/-- **Comparison-sort lower bound for `n` elements**: any comparison decision tree that
sorts every input of length `n` has depth at least `⌈log₂ (n !)⌉`. -/
theorem sorting_lb {n : ℕ} (t : DTree n) (hsort : ∀ σ : Equiv.Perm (Fin n), run t σ = σ) :
    Nat.clog 2 (Nat.factorial n) ≤ depth t := by
  have h : Nat.factorial n ≤ 2 ^ depth t := (factorial_le_length_leaves t hsort).trans (length_leaves_le t)
  exact (Nat.clog_le_iff_le_pow (by norm_num)).2 h

/-- **Any comparison sort of 4 elements needs at least `⌈log₂(4!)⌉ = 5` comparisons in the
worst case.** -/
theorem sorting_lb_4 (t : DTree 4) (hsort : ∀ σ : Equiv.Perm (Fin 4), run t σ = σ) :
    Nat.clog 2 (Nat.factorial 4) ≤ depth t ∧ Nat.clog 2 (Nat.factorial 4) = 5 := by
  refine ⟨sorting_lb t hsort, ?_⟩
  norm_num [Nat.factorial]

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

