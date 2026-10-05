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

theorem barrington :
    (∀ (n : ℕ) (_i₀ : Fin n) (f : Formula n) (σ : Perm (Fin 5)), IsFiveCycle σ →
        ∃ P : Program n, P.length ≤ 4 ^ f.depth ∧ P.Computes σ f.eval)
    ∧ (∀ (n k : ℕ) (P : Program n) (σ : Perm (Fin 5)), P.length ≤ 2 ^ k →
        ∃ ψ : Formula n, ψ.depth ≤ 6 * k + 4 ∧ ∀ x, ((ψ.eval x = true) ↔ P.eval x = σ)) :=
  ⟨fun _ i₀ f σ hσ => barrington_forward i₀ f σ hσ,
   fun _ k P σ hP => barrington_converse k P σ hP⟩

end CS

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

