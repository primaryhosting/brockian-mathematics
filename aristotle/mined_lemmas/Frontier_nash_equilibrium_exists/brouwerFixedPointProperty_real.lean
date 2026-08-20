import RequestProject.Nash

/-!
# The one-dimensional base case of Brouwer's fixed point theorem

Brouwer's fixed point theorem is not available in Mathlib, and is taken as an explicit
hypothesis in `Frontier.nash_equilibrium_exists`.  Here we prove the one-dimensional base
case of that hypothesis, `BrouwerFixedPointProperty ℝ`, from the intermediate value
theorem; in particular the hypothesis is not vacuous.
-/

open Set

namespace Frontier

/-- **Brouwer's fixed point theorem in dimension one**: every continuous self-map of a
nonempty compact convex subset of `ℝ` has a fixed point. -/

theorem brouwerFixedPointProperty_real : BrouwerFixedPointProperty ℝ := by
  intro K hne hcomp hconv f hf hmaps
  obtain ⟨a, haK, hamin⟩ := hcomp.exists_isLeast hne
  obtain ⟨b, hbK, hbmax⟩ := hcomp.exists_isGreatest hne
  have hKsub : K ⊆ Set.Icc a b := fun x hx => ⟨hamin hx, hbmax hx⟩
  have hIcc : Set.Icc a b ⊆ K := fun x hx => hconv.ordConnected.out haK hbK hx
  have hKeq : K = Set.Icc a b := Set.Subset.antisymm hKsub hIcc
  have hab : a ≤ b := hamin hbK
  have hcont : ContinuousOn (fun x => f x - x) (Set.Icc a b) := by
    rw [← hKeq]
    exact hf.sub continuousOn_id
  have hga : 0 ≤ f a - a := by
    have := hKsub (hmaps haK)
    simp only [Set.mem_Icc] at this
    linarith [this.1]
  have hgb : f b - b ≤ 0 := by
    have := hKsub (hmaps hbK)
    simp only [Set.mem_Icc] at this
    linarith [this.2]
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hab hcont ⟨hgb, hga⟩
  exact ⟨c, hKeq ▸ hc, by linarith [hc0]⟩

end Frontier

import RequestProject.ZeroSum

/-!
# Zero-sum two-player games inside the general framework

The saddle point theorem of `RequestProject.ZeroSum` is transported to the general finite
game framework of `RequestProject.Nash`: a two-player game is one indexed by `Bool`, and a
zero-sum one has `u true = - u false`.  The conclusion is the *unconditional* existence of a
mixed strategy Nash equilibrium in the sense of `Frontier.IsNashEquilibrium`.
-/

open Finset Function Set

namespace Frontier

variable {S : Bool → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]

/-- A profile of two players is a pair of strategies. -/
