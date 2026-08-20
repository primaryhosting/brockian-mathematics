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

theorem exists_formula_of_bp {n : ℕ} (P : List (Instr n)) (A : Finset Perm5) :
    ∃ φ : Formula n, (∀ x, (φ.eval x = true ↔ BPeval P x ∈ A)) ∧
      φ.depth ≤ (K5 + 1) * Nat.clog 2 P.length + 1 + K5 := by
  choose φ hφ hd using fun π => exists_formula_eq n P.length P rfl π
  refine ⟨Formula.orList (A.toList.map φ), ?_, ?_⟩
  · intro x
    rw [Formula.eval_orList]
    simp only [List.any_map, List.any_eq_true, Function.comp_def, Finset.mem_toList]
    constructor
    · rintro ⟨π, hπ, h⟩
      rw [(hφ π x).1 h]; exact hπ
    · intro h
      exact ⟨BPeval P x, h, (hφ _ x).2 rfl⟩
  · have hor := Formula.depth_orList (A.toList.map φ) ((K5 + 1) * Nat.clog 2 P.length + 1)
      (by
        intro p hp
        simp only [List.mem_map, Finset.mem_toList] at hp
        obtain ⟨π, -, rfl⟩ := hp
        exact hd π)
    rw [List.length_map] at hor
    have := card_le_K5 A
    omega

end CS

import RequestProject.Basic

/-!
# Barrington's theorem, the hard direction

Every boolean formula of depth `d` is computed, in Barrington normal form with respect to
any prescribed five-cycle, by a width-5 permutation branching program of length at most
`4 ^ d`.
-/

namespace CS

open Equiv Equiv.Perm

/-! ### A commutator of five-cycles which is again a five-cycle -/

/-- A distinguished five-cycle. -/
