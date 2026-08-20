/-
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Barrington's theorem

We formalise Barrington's theorem: the class of Boolean function families computed by
logarithmic-depth fan-in-two Boolean circuits (`NC¹`) coincides with the class of families
computed by polynomial-length width-`5` permutation branching programs.

* `CS.Barrington.Circuit` : fan-in two Boolean circuits over `{¬, ∧, ∨}` and constants.
* `CS.Barrington.Instr`, `CS.Barrington.run` : width-5 permutation branching programs,
  i.e. lists of instructions, each of which multiplies the running value in `S₅` by a
  permutation depending on (at most) one input bit.
* `CS.Barrington.NC1` and `CS.Barrington.W5BP` : the two classes.
* `CS.barrington` : the two classes are equal.
-/

namespace CS
namespace Barrington

open Equiv

/-- The symmetric group on five points. -/
abbrev Perm5 := Equiv.Perm (Fin 5)

/-! ### Boolean circuits -/

/-- Fan-in two Boolean circuits (formulas) on `n` inputs. -/
inductive Circuit (n : ℕ) where
  | var : Fin n → Circuit n
  | const : Bool → Circuit n
  | not : Circuit n → Circuit n
  | and : Circuit n → Circuit n → Circuit n
  | or : Circuit n → Circuit n → Circuit n

/-- The Boolean function computed by a circuit. -/

lemma exists_conj_commutator (ρ : Perm5) :
    ∃ a b : Perm5,
      (a * c5 * a⁻¹) * (b * c5 * b⁻¹) * (a * c5 * a⁻¹)⁻¹ * (b * c5 * b⁻¹)⁻¹ = ρ * c5 * ρ⁻¹ := by
  obtain ⟨u, hu⟩ : ∃ u : Perm5, u * c5 * u⁻¹ = List.formPerm [2, 1, 3, 0, 4] := by decide
  obtain ⟨v, hv⟩ : ∃ v : Perm5, v * c5 * v⁻¹ = List.formPerm [2, 0, 1, 3, 4] := by decide
  have key : (List.formPerm [2, 1, 3, 0, 4] : Perm5) * (List.formPerm [2, 0, 1, 3, 4]) *
      (List.formPerm [2, 1, 3, 0, 4] : Perm5)⁻¹ * (List.formPerm [2, 0, 1, 3, 4] : Perm5)⁻¹
      = c5 := by decide
  refine ⟨ρ * u, ρ * v, ?_⟩
  have e1 : (ρ * u) * c5 * (ρ * u)⁻¹ = ρ * (List.formPerm [2, 1, 3, 0, 4] : Perm5) * ρ⁻¹ := by
    rw [← hu]; group
  have e2 : (ρ * v) * c5 * (ρ * v)⁻¹ = ρ * (List.formPerm [2, 0, 1, 3, 4] : Perm5) * ρ⁻¹ := by
    rw [← hv]; group
  rw [e1, e2, ← key]
  group

/-! ### From circuits to branching programs (Barrington's construction) -/

/-- There is a program of length at most `N` computing `f` with distinguished
permutation `σ`. -/
