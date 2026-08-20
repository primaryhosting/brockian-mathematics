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

theorem exists_commutator_eq (σ : Perm5) (hσ : IsFiveCycle σ) :
    ∃ α β : Perm5, IsFiveCycle α ∧ IsFiveCycle β ∧ α * β * α⁻¹ * β⁻¹ = σ := by
  obtain ⟨ρ, hρ⟩ := isFiveCycle_sigma0.exists_conj hσ
  refine ⟨ρ * alpha0 * ρ⁻¹, ρ * beta0 * ρ⁻¹, isFiveCycle_alpha0.conj ρ,
    isFiveCycle_beta0.conj ρ, ?_⟩
  rw [← hρ, ← commutator_alpha0_beta0]
  group

/-! ### Multiplying the output of a program by a constant on the left -/

/-- Multiply the permutations produced by an instruction by `τ` on the left. -/
