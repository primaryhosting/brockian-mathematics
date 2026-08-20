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

theorem CompTree.outputs_eq_univ {n : ℕ} (t : CompTree n) (h : t.Sorts) :
    t.outputs = Finset.univ := by
  refine Finset.eq_univ_of_forall ?_
  intro q
  set s : Equiv.Perm (Fin n) := q⁻¹ with hs
  set a : Fin n → ℕ := fun i => ((s i : Fin n) : ℕ) with ha
  have hinj : Function.Injective a := by
    intro x y hxy
    simp only [ha] at hxy
    exact s.injective (Fin.ext hxy)
  have hmono := h a hinj
  set p := run a t with hp
  have hsm : StrictMono ((p.trans s) : Fin n → Fin n) := by
    intro x y hxy
    have hlt := hmono hxy
    exact Fin.lt_def.mpr hlt
  have heq := strictMono_perm_eq_refl _ hsm
  have hpq : p = q := by
    have := congrArg (fun f => Equiv.trans f s.symm) heq
    simpa [hs, Equiv.trans_assoc] using this
  rw [← hpq, hp]
  exact run_mem_outputs a t

/-!
### Non-vacuity: comparison trees that sort `4` elements do exist

To confirm that the hypothesis `Sorts` is satisfiable (so the lower bound is not vacuous), we
build an explicit (very inefficient) comparison tree that sorts `4` elements: it scans over all
permutations, checking each one with three comparisons, and outputs the first that works.
-/

/-- `a ∘ q` is nondecreasing along the consecutive indices of `Fin 4`. -/
