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

lemma prod_update (x : ∀ i, S i → ℝ) (i : ι) (y : S i → ℝ) (p : ∀ i, S i) :
    (∏ j, Function.update x i y j (p j))
      = y (p i) * ∏ j ∈ Finset.univ \ {i}, x j (p j) := by
  have h : (fun j => Function.update x i y j (p j))
      = Function.update (fun j => x j (p j)) i (y (p i)) := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_of_ne h]
  rw [show (∏ j, Function.update x i y j (p j))
      = ∏ j, Function.update (fun j => x j (p j)) i (y (p i)) j from by rw [h]]
  exact Finset.prod_update_of_mem (Finset.mem_univ i) _ _

omit [∀ i, Nonempty (S i)] in
/-- The expected payoff is linear in the deviating player's own mixed strategy. -/
