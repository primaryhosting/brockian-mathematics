/-
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset

/-! ## Finite games in normal form -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- A probability distribution on the (finite) pure strategy set of a player. -/

lemma prod_update_eq {i : ι} (x : ∀ j, S j → ℝ) (z : S i → ℝ) (p : ∀ j, S j) :
    (∏ j, (Function.update x i z) j (p j))
      = z (p i) * ∏ j ∈ univ.erase i, x j (p j) := by
  rw [← Finset.mul_prod_erase univ (fun j => (Function.update x i z) j (p j)) (mem_univ i)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

omit [∀ i, DecidableEq (S i)] in
