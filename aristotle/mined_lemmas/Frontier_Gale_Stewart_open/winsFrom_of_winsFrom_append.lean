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

lemma winsFrom_of_winsFrom_append (a₀ : A) (W : Set (ℕ → A)) (p : List A)
    (hp : Even p.length) (a : A) (h : WinsFrom a₀ W (p ++ [a])) : WinsFrom a₀ W p := by
  obtain ⟨σ, hσ⟩ := h
  classical
  refine ⟨fun q => if q = p then a else σ q, fun τ => ?_⟩
  set σ' : List A → A := fun q => if q = p then a else σ q with hσ'
  have key : ∀ n : ℕ, run σ' τ p (n + 1) = run σ τ (p ++ [a]) (n + 0) := by
    intro n
    induction n with
    | zero =>
        show run σ' τ p 0 ++ [nextMove σ' τ (run σ' τ p 0)] = _
        simp [run, nextMove, hp, hσ']
    | succ n ih =>
        show run σ' τ p (n + 1) ++ [nextMove σ' τ (run σ' τ p (n + 1))] = _
        simp only [Nat.add_zero] at ih ⊢
        rw [ih]
        have hlen : p.length < (run σ τ (p ++ [a]) n).length := by
          rw [run_length]; simp; omega
        have hne : run σ τ (p ++ [a]) n ≠ p := by
          intro hcon
          rw [hcon] at hlen
          exact lt_irrefl _ hlen
        show _ = run σ τ (p ++ [a]) n ++ [nextMove σ τ (run σ τ (p ++ [a]) n)]
        simp [nextMove, hσ', hne]
  have := play_ext_of_run_eq (a₀ := a₀) (σ := σ') (τ := τ) (σ' := σ) (τ' := τ)
    (p := p) (q := p ++ [a]) (m := 1) (k := 0) key
  rw [this]
  exact hσ τ

/-- If it is player II's turn at `p` and player I can win from `p ++ [a]` for every move `a`,
then player I can win from `p`. -/
