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

/-!
# Information-theoretic lower bound for comparison sorting of 4 elements

We model a comparison-based sorting algorithm on `n` inputs as a binary decision tree
(`CS.CompTree n`): each internal node compares two input positions `i j` (asking `a i ≤ a j`)
and branches accordingly; each leaf outputs a permutation, which is meant to list the input
positions in sorted order.

A tree *sorts* if, for every injective input `a : Fin n → ℕ`, the output permutation `p`
satisfies that `a ∘ p` is strictly monotone.

The main theorem `CS.sorting_lb_4` states that any comparison tree that sorts `4` elements has
depth at least `⌈log₂ (4!)⌉ = 5`, i.e. it performs at least 5 comparisons in the worst case.
-/

namespace CS

/-- A comparison-based decision tree on `n` inputs: internal nodes compare two positions,
leaves output a permutation. -/
inductive CompTree (n : ℕ) : Type
  | leaf : Equiv.Perm (Fin n) → CompTree n
  | node : Fin n → Fin n → CompTree n → CompTree n → CompTree n

namespace CompTree

variable {n : ℕ}

/-- The depth of a comparison tree: the worst-case number of comparisons performed. -/

theorem chain4_of_run_foldr (a : Fin 4 → ℕ) (l : List (Equiv.Perm (Fin 4)))
    (base : CompTree 4) (h : ∃ q ∈ l, Chain4 a q) :
    Chain4 a (CompTree.run a (l.foldr check4 base)) := by
  induction l with
  | nil => simp at h
  | cons q l ih =>
      rw [List.foldr_cons, run_check4]
      split_ifs with hq
      · exact hq
      · refine ih ?_
        obtain ⟨r, hr, hcr⟩ := h
        rcases List.mem_cons.1 hr with rfl | hr'
        · exact absurd hcr hq
        · exact ⟨r, hr', hcr⟩

