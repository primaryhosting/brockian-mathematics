import Mathlib

/-!
# Basic definitions for Barrington's theorem

* Boolean formulas over the basis `{¬, ∧, ∨}` (with constants), together with their
  depth and semantics.  Non-uniform `NC¹` is the class of families of boolean functions
  computed by formulas of logarithmic depth.
* Width-5 permutation branching programs: a program is a list of instructions, each of
  which reads one input bit and outputs one of two permutations of `Fin 5` (or is a
  constant instruction).  The value of the program is the product of the permutations
  produced by its instructions, and the program accepts iff this product lies in a
  designated set of accepting permutations.
-/

namespace CS

open Equiv Equiv.Perm

/-- Permutations of a five element set. -/
abbrev Perm5 := Equiv.Perm (Fin 5)

/-- A permutation of `Fin 5` is a five-cycle if it is a cycle whose support is everything. -/

theorem isFiveCycle_formPerm (l : List (Fin 5)) (hl : l.Nodup) (h5 : l.length = 5) :
    IsFiveCycle l.formPerm := by
  refine ⟨List.isCycle_formPerm hl (by omega), ?_⟩
  rw [List.support_formPerm_of_nodup l hl (by rintro x rfl; simp at h5)]
  rw [List.toFinset_card_of_nodup hl, h5]

/-- Boolean formulas in `n` variables over the basis `{¬, ∧, ∨}` with constants. -/
inductive Formula (n : ℕ) : Type
  | const : Bool → Formula n
  | var : Fin n → Formula n
  | not : Formula n → Formula n
  | and : Formula n → Formula n → Formula n
  | or : Formula n → Formula n → Formula n

/-- The boolean function computed by a formula. -/
