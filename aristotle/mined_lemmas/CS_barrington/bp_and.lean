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

theorem bp_and {n : ℕ} {P₁ P₂ P₃ P₄ : List (Instr n)} {α β : Perm5}
    {f g : (Fin n → Bool) → Bool}
    (h1 : Computes P₁ α f) (h2 : Computes P₂ β g)
    (h3 : Computes P₃ α⁻¹ f) (h4 : Computes P₄ β⁻¹ g) :
    Computes (P₁ ++ P₂ ++ P₃ ++ P₄) (α * β * α⁻¹ * β⁻¹) (fun x => f x && g x) := by
  intro x
  rw [BPeval_append, BPeval_append, BPeval_append, h1 x, h2 x, h3 x, h4 x]
  cases hf : f x <;> cases hg : g x <;> simp [hf, hg, mul_assoc]

/-! ### Barrington's construction -/

/-- **Barrington's theorem** (hard direction): a formula of depth `d` is computed by a
width-5 permutation branching program of length at most `4 ^ d`, in normal form with
respect to any prescribed five-cycle. -/
