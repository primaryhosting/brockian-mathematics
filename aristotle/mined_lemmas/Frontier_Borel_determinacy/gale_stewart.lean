import Mathlib

/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
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

/-! ## Infinite games: positions, strategies, winning strategies

We consider infinite two-player games with perfect information played on an alphabet `X`.
A *play* is a sequence `x : ℕ → X`; the move at time `n` is `x n`.  Which player moves at
time `n` is recorded by a predicate `turn : ℕ → Prop` (the *turn set* of the player under
consideration).  In the classical game `G(A)` on Baire space, player I moves at the even
times and player II at the odd times, and player I wins the play `x` iff `x ∈ A`.
-/

variable {X : Type*}

/-- The position reached after the first `n` moves of the play `x`. -/

theorem gale_stewart [Inhabited X] (turn : ℕ → Prop) (A : Set (ℕ → X)) (hA : CylClosed A) :
    WinsFrom turn A [] ∨ WinsFrom (fun n => ¬ turn n) Aᶜ [] := by
  classical
  by_cases h0 : WinsFrom (fun n => ¬ turn n) Aᶜ ([] : List X)
  · exact Or.inr h0
  left
  set W : List X → Prop := fun p => WinsFrom (fun n => ¬ turn n) Aᶜ p
  -- from a position not won by the opponent, some move keeps it so
  have step_our : ∀ p : List X, ¬ W p → ∃ a : X, ¬ W (p ++ [a]) := by
    intro p hnp
    by_contra hcon
    push_neg at hcon
    exact hnp (winsFrom_of_forall_moves (fun a => hcon a))
  -- and if it is the opponent's move, *every* move keeps it so
  have step_their : ∀ (p : List X) (a : X), ¬ turn p.length → ¬ W p → ¬ W (p ++ [a]) := by
    intro p a hturn hnp hwa
    exact hnp (winsFrom_of_move (turn := fun n => ¬ turn n) (by simpa using hturn) hwa)
  refine ⟨fun q => if h : ∃ a : X, ¬ W (q ++ [a]) then h.choose else default, ?_⟩
  intro x _hx hfol
  set σ : List X → X := fun q => if h : ∃ a : X, ¬ W (q ++ [a]) then h.choose else default
    with hσ
  have key : ∀ n, ¬ W (pre x n) := by
    intro n
    induction n with
    | zero => simpa [pre] using h0
    | succ n ih =>
      rw [pre_succ]
      by_cases hturn : turn n
      · obtain ⟨a, ha⟩ := step_our (pre x n) ih
        have hex : ∃ a : X, ¬ W (pre x n ++ [a]) := ⟨a, ha⟩
        have hxn : x n = σ (pre x n) := hfol n (by simp) hturn
        rw [hxn, hσ]
        simp only [dif_pos hex]
        exact hex.choose_spec
      · have hlen : (pre x n).length = n := by simp
        exact step_their (pre x n) (x n) (by rw [hlen]; exact hturn) ih
  by_contra hxA
  obtain ⟨n, hn⟩ := hA x hxA
  exact key n (winsFrom_of_forall (fun y hy => hn y hy))

/-- Games with a closed payoff set (on any alphabet) are determined. -/
