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

theorem BPeval_lmulBP {n : ℕ} (τ : Perm5) (P : List (Instr n)) (x : Fin n → Bool) :
    BPeval (lmulBP τ P) x = τ * BPeval P x := by
  cases P with
  | nil => simp [lmulBP, Instr.run, BPeval]
  | cons I t =>
      cases I with
      | test i p q =>
          by_cases h : x i <;> simp [lmulBP, Instr.lmul, Instr.run, h, mul_assoc]
      | const p => simp [lmulBP, Instr.lmul, Instr.run, mul_assoc]

