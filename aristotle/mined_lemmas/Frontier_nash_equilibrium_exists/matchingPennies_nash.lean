/-
Two player zero sum finite games: the von Neumann minimax theorem, proved
unconditionally (via the separating hyperplane theorem, without Brouwer).
This is the unconditional "base case" of Nash's theorem.
-/

import RequestProject.NashEquilibrium

/-!
# Minimax for two player zero sum finite games
-/

open scoped BigOperators

namespace Frontier

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The vector of expected payoffs to the row player against the mixed strategy `y`. -/

theorem matchingPennies_nash :
    IsNash (zeroSumGame matchingPennies) (twoMixed uniformBool uniformBool) := by
  have hmix : IsMixed (twoMixed uniformBool uniformBool) := by
    intro b
    cases b <;> exact uniformBool_mem_stdSimplex
  have hbilin : ∀ x : Bool → ℝ, bilin matchingPennies x uniformBool = 0 := by
    intro x
    simp [bilin, matchingPennies, uniformBool]
  have hbilin' : ∀ y : Bool → ℝ, bilin matchingPennies uniformBool y = 0 := by
    intro y
    simp [bilin, matchingPennies, uniformBool]
    ring
  rw [isNash_iff _ hmix]
  intro b s
  cases b
  · rw [devPayoff, expectedPayoff_zeroSum_false, expectedPayoff_zeroSum_false]
    have h1 : (Function.update (twoMixed uniformBool uniformBool)
        false (pureVec s)) true = uniformBool := rfl
    have h2 : (Function.update (twoMixed uniformBool uniformBool)
        false (pureVec s)) false = pureVec s := Function.update_self _ _ _
    rw [h1, h2, hbilin' (pureVec s), twoMixed_true, twoMixed_false, hbilin']
  · rw [devPayoff, expectedPayoff_zeroSum_true, expectedPayoff_zeroSum_true]
    have h1 : (Function.update (twoMixed uniformBool uniformBool)
        true (pureVec s)) true = pureVec s := Function.update_self _ _ _
    have h2 : (Function.update (twoMixed uniformBool uniformBool)
        true (pureVec s)) false = uniformBool := rfl
    rw [h1, h2, hbilin (pureVec s), twoMixed_true, twoMixed_false, hbilin]

end Frontier

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

open scoped BigOperators

namespace Frontier

/-- A finite game in normal form: a finite set of players `ι`, a finite set of
pure strategies `S i` for each player, and a real payoff for each player at each pure
strategy profile. -/
structure FiniteGame (ι : Type) [Fintype ι] [DecidableEq ι]
    (S : ι → Type) [∀ i, Fintype (S i)] where
  payoff : ι → ((i : ι) → S i) → ℝ

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- A mixed strategy profile: each player's mixed strategy lies in the standard simplex. -/
