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

namespace Frontier

section GaleStewart

variable {A : Type*}

/-- In a two–player game on the move set `A`, the players alternate moves, player I moving at
positions of even length and player II at positions of odd length.  Given strategies `σ` for
player I and `τ` for player II, `nextMove σ τ p` is the move played at the position `p`. -/

lemma run_getD_eq_play (a₀ : A) (σ τ : List A → A) (p : List A) (n i : ℕ)
    (hi : i < p.length + n) : (run σ τ p n).getD i a₀ = play a₀ σ τ p i := by
  induction n with
  | zero =>
      have : i < p.length := by simpa using hi
      simp [run, play, this]
  | succ n ih =>
      rcases lt_or_ge i (p.length + n) with h | h
      · have hlen : i < (run σ τ p n).length := by rw [run_length]; exact h
        rw [show run σ τ p (n + 1)
              = run σ τ p n ++ [nextMove σ τ (run σ τ p n)] from rfl,
          List.getD_append _ _ _ _ hlen]
        exact ih h
      · have hi' : i = p.length + n := by omega
        subst hi'
        rw [show run σ τ p (n + 1)
              = run σ τ p n ++ [nextMove σ τ (run σ τ p n)] from rfl]
        rw [List.getD_append_right _ _ _ _ (by rw [run_length]), run_length]
        simp [play_length_add]

/-- Two plays that agree on the first `n` moves. -/
