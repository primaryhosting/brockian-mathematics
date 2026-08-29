import Mathlib

/-!
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Set

namespace Frontier

universe u

/-! ## Finite games in mixed strategies

A finite game is given by a finite type of players `I`, a finite nonempty type of pure
strategies `S i` for each player, and a real payoff function
`u : I → ((i : I) → S i) → ℝ`.
-/

variable {I : Type u} [Fintype I] [DecidableEq I]
  {S : I → Type u} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The set of mixed strategy profiles: for each player, a probability distribution on
that player's pure strategies. -/

theorem nash_equilibrium_exists_of_subsingleton [Subsingleton I] [∀ i, Nonempty (S i)]
    (u : I → ((i : I) → S i) → ℝ) :
    ∃ σ ∈ mixedProfiles S, IsNashEquilibrium u σ := by
  -- with at most one player, the product over the other players is empty
  have hprod : ∀ (i : I) (σ : (i : I) → S i → ℝ) (s : (i : I) → S i),
      ∏ j ∈ univ.erase i, σ j (s j) = 1 := fun i σ s =>
    Finset.prod_eq_one fun j hj => absurd (Subsingleton.elim j i) (Finset.ne_of_mem_erase hj)
  -- hence the payoff from a pure deviation does not depend on the profile at all
  have hdev : ∀ (i : I) (a : S i) (σ σ' : (i : I) → S i → ℝ),
      dev u i a σ = dev u i a σ' := by
    intro i a σ σ'
    simp only [dev, payoff, prod_update_apply, hprod]
  choose a ha using fun i : I => Finite.exists_max (fun b : S i => dev u i b (fun _ _ => 0))
  refine ⟨fun i => pureMix (a i), ?_, ?_⟩
  · rw [mem_mixedProfiles_iff]
    refine fun i => ⟨fun b => ?_, ?_⟩
    · simp only [pureMix]; positivity
    · simp [pureMix]
  · refine isNashEquilibrium_of_dev_le u _ fun i b => ?_
    rw [payoff_eq_sum_dev, show (∑ c : S i, pureMix (a i) c *
        dev u i c (fun i => pureMix (a i)))
        = dev u i (a i) (fun i => pureMix (a i)) by simp [pureMix]]
    rw [hdev i b _ (fun _ _ => 0), hdev i (a i) _ (fun _ _ => 0)]
    exact ha i b

end Frontier

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

