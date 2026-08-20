/-
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace GaleStewart

universe u

variable {X : Type u}

/-- The list of the first `n` moves of the play `a`. -/

theorem Gale_Stewart_open {X : Type u} [Nonempty X] [TopologicalSpace X] [DiscreteTopology X]
    (A : Set (ℕ → X)) (hA : IsOpen A) :
    (∃ σ : List X → X, ∀ a : ℕ → X, FollowsI σ a → a ∈ A) ∨
      (∃ τ : List X → X, ∀ a : ℕ → X, FollowsII τ a → a ∉ A) := by
  -- `W` is the set of finite positions that already force a win for player I
  set W : Set (List X) := {p : List X | ∀ b : ℕ → X, hist b p.length = p → b ∈ A} with hW
  have hWA : ∀ (a : ℕ → X) (m : ℕ), hist a m ∈ W → a ∈ A := by
    intro a m hm
    exact hm a (by simp)
  have hAW : ∀ a : ℕ → X, a ∈ A → ∃ m, hist a m ∈ W := by
    intro a ha
    obtain ⟨n, hn⟩ := isOpen_forcing hA ha
    refine ⟨n, fun b hb => hn b ?_⟩
    intro i hi
    exact eq_of_hist_eq (by simpa using hb) i hi
  rcases isEmpty_or_nonempty (WinT W ([] : List X)) with hE | hne
  · right
    obtain ⟨τ, hτ⟩ := no_winT_strategy hE
    refine ⟨τ, ?_⟩
    intro a ha haA
    obtain ⟨m, hm⟩ := hAW a haA
    exact hτ a ha m hm
  · left
    obtain ⟨t⟩ := hne
    obtain ⟨σ, hσ⟩ := winT_strategy t
    refine ⟨σ, fun a ha => ?_⟩
    obtain ⟨m, hm⟩ := hσ a (by simp) (fun n _ hn => ha n hn)
    exact hWA a m hm

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

