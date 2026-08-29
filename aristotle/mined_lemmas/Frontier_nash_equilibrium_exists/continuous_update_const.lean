/-
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not permit a module docstring before the `import` line; the required
header is reproduced verbatim below as the module docstring.)
-/

import Mathlib

/-!
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

open Finset Set

/-! ## Finite games in normal form -/

section Defs

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The set of mixed strategy profiles of a finite game: for each player `i` a probability
distribution on that player's (finite) pure strategy set `S i`. -/

lemma continuous_update_const (i : ι) (c : S i → ℝ) :
    Continuous fun x : (∀ i, S i → ℝ) => Function.update x i c := by
  refine continuous_pi fun j => ?_
  by_cases h : j = i
  · subst h
    simpa using continuous_const
  · simpa only [Function.update_of_ne h] using continuous_apply j

/-- The gain player `i` would obtain by switching to the pure strategy `s`. -/
