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

theorem strictMono_of_chain4 (a : Fin 4 → ℕ) (hinj : Function.Injective a)
    (q : Equiv.Perm (Fin 4)) (h : Chain4 a q) : StrictMono (a ∘ (q : Fin 4 → Fin 4)) := by
  refine Monotone.strictMono_of_injective ?_ (hinj.comp q.injective)
  rw [Fin.monotone_iff_le_succ]
  intro i
  fin_cases i
  · simpa using h.1
  · simpa using h.2.1
  · simpa using h.2.2

/-- There is a comparison tree that sorts `4` elements, so the lower bound below is not vacuous. -/
