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

lemma play_ext_of_run_eq {a₀ : A} {σ τ σ' τ' : List A → A} {p q : List A} {m k : ℕ}
    (h : ∀ n : ℕ, run σ τ p (n + m) = run σ' τ' q (n + k)) :
    play a₀ σ τ p = play a₀ σ' τ' q := by
  funext i
  have h1 : i < p.length + (i + 1 + m) := by omega
  have h2 : i < q.length + (i + 1 + k) := by omega
  rw [← run_getD_eq_play a₀ σ τ p (i + 1 + m) i h1,
    ← run_getD_eq_play a₀ σ' τ' q (i + 1 + k) i h2, h (i + 1)]

/-- If player I can win from `p ++ [a]`, then he can win from `p`, provided it is his turn at `p`
(so that he can play `a`). -/
