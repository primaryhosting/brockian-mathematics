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

theorem nash_equilibrium_exists_of_potential [∀ i, Nonempty (S i)]
    (u : ι → (∀ j, S j) → ℝ) (P : (∀ j, S j) → ℝ)
    (hP : ∀ (i : ι) (p : ∀ j, S j) (s : S i),
      u i (Function.update p i s) - u i p = P (Function.update p i s) - P p) :
    ∃ x : ∀ j, S j → ℝ, IsNashEquilibrium u x := by
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image (univ : Finset (∀ j, S j)) P
    ⟨Classical.arbitrary _, mem_univ _⟩
  refine ⟨pureProfile p, isNashEquilibrium_of_pure u (isMixed_pureProfile p) ?_⟩
  intro i s
  rw [devPayoff_pureProfile, payoff_pureProfile]
  have h1 := hP i p s
  have h2 : P (Function.update p i s) ≤ P p := hp _ (mem_univ _)
  linarith

/-- A concrete instance, showing the definitions are satisfiable: the two-player
coordination game on `Bool` (both players get `1` if they choose the same action and `0`
otherwise) has a Nash equilibrium. -/
