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

We formalise Barrington's theorem, which identifies `NC¹` (log-depth boolean formulas)
with width-`5` permutation branching programs:

* **Forward direction.** Every boolean formula of depth `d` is computed by a width-`5`
  permutation branching program of length at most `4 ^ d` (in the strong sense of
  `σ`-computation, for an arbitrary `5`-cycle `σ`).
* **Converse direction.** Every width-`5` permutation branching program of length at
  most `2 ^ k` is computed by a boolean formula of depth `O(k)` (explicitly `6 * k + 4`).

Together these say: depth-`d` formulas ↔ length-`4^d` width-`5` programs, i.e.
`NC¹` = width-`5` permutation branching programs.
-/

namespace CS

open Equiv Equiv.Perm

/-! ### Boolean formulas -/

/-- Boolean formulas in `n` variables, over the complete basis `{¬, ∧}` together with
constants.  Depth-`O(log n)` formulas are exactly `NC¹`. -/
inductive Formula (n : ℕ) where
  | const : Bool → Formula n
  | var : Fin n → Formula n
  | not : Formula n → Formula n
  | and : Formula n → Formula n → Formula n
  deriving DecidableEq

variable {n : ℕ}

/-- The boolean function computed by a formula. -/

theorem exists_commutator {γ : Perm (Fin 5)} (hγ : IsFiveCycle γ) :
    ∃ σ τ : Perm (Fin 5), IsFiveCycle σ ∧ IsFiveCycle τ ∧ σ * τ * σ⁻¹ * τ⁻¹ = γ := by
  have hτ0 : IsFiveCycle tau0 := isFiveCycle_conj isFiveCycle_c5 _
  have hγ0 : IsFiveCycle (c5 * tau0 * c5⁻¹ * tau0⁻¹) := by
    rw [← pi0_conj]; exact isFiveCycle_conj isFiveCycle_c5 _
  obtain ⟨ρ, hρ⟩ := isConj_iff.1 (isConj_of_isFiveCycle hγ0 hγ)
  refine ⟨ρ * c5 * ρ⁻¹, ρ * tau0 * ρ⁻¹, isFiveCycle_conj isFiveCycle_c5 _,
    isFiveCycle_conj hτ0 _, ?_⟩
  rw [← hρ]; group

/-! ### Forward direction: formulas to programs -/

