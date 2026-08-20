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

lemma winsFrom_of_forall_winsFrom_append (a₀ : A) (W : Set (ℕ → A)) (p : List A)
    (hp : ¬ Even p.length) (h : ∀ a : A, WinsFrom a₀ W (p ++ [a])) : WinsFrom a₀ W p := by
  classical
  choose f hf using h
  refine ⟨fun q => f (q.getD p.length a₀) q, fun τ => ?_⟩
  set σ : List A → A := fun q => f (q.getD p.length a₀) q with hσdef
  set b : A := τ p with hb
  have hpb : (p ++ [b]).length = p.length + 1 := by simp
  have hgetb : ∀ n : ℕ, (run (f b) τ (p ++ [b]) n).getD p.length a₀ = b := by
    intro n
    rw [run_getD_of_lt a₀ (f b) τ (p ++ [b]) n p.length (by rw [hpb]; omega)]
    simp
  have key : ∀ n : ℕ, run σ τ p (n + 1) = run (f b) τ (p ++ [b]) (n + 0) := by
    intro n
    induction n with
    | zero =>
        show run σ τ p 0 ++ [nextMove σ τ (run σ τ p 0)] = _
        simp [run, nextMove, hp, hb]
    | succ n ih =>
        show run σ τ p (n + 1) ++ [nextMove σ τ (run σ τ p (n + 1))] = _
        simp only [Nat.add_zero] at ih ⊢
        rw [ih]
        show _ = run (f b) τ (p ++ [b]) n ++ [nextMove (f b) τ (run (f b) τ (p ++ [b]) n)]
        simp only [nextMove, hσdef, hgetb n]
  have := play_ext_of_run_eq (a₀ := a₀) (σ := σ) (τ := τ) (σ' := f b) (τ' := τ)
    (p := p) (q := p ++ [b]) (m := 1) (k := 0) key
  rw [this]
  exact hf b τ

/-- A defensive strategy for player II: at a position from which player I has no winning
strategy, play a move preserving that fact. -/
