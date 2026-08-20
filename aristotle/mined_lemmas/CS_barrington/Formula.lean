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

theorem Formula.depth_orList {n : ℕ} (L : List (Formula n)) (D : ℕ)
    (h : ∀ p ∈ L, p.depth ≤ D) : (Formula.orList L).depth ≤ D + L.length := by
  induction L with
  | nil => simp [Formula.orList, Formula.depth]
  | cons p t ih =>
      have h1 : p.depth ≤ D := h p (by simp)
      have h2 := ih (fun q hq => h q (by simp [hq]))
      simp only [Formula.orList, Formula.depth, List.length_cons]
      omega

/-- An instruction of a width-5 permutation branching program: either it reads the input
bit `i` and produces `p` or `q` accordingly, or it produces a fixed permutation. -/
inductive Instr (n : ℕ) : Type
  | test : Fin n → Perm5 → Perm5 → Instr n
  | const : Perm5 → Instr n

/-- The permutation produced by an instruction on a given input. -/
