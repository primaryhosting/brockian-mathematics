/-
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

variable {A : Type*}

/-- The finite position consisting of the first `n` moves of the play `x`. -/

lemma noWinI_of_moveI {p : List A} (hp : Even p.length)
    (h : ¬ ∃ σ : List A → A, WinningI W σ p) (a : A) :
    ¬ ∃ σ : List A → A, WinningI W σ (p ++ [a]) := by
  rintro ⟨σ, hσ⟩
  refine h ⟨fun q => if q.length = p.length then a else σ q, ?_⟩
  intro x hx
  obtain ⟨hext, hmove⟩ := hx
  have hxa : x p.length = a := by simpa using hmove p.length le_rfl hp
  refine hσ x ⟨extends_append_singleton hext hxa, ?_⟩
  intro n hn hne
  simp only [List.length_append, List.length_singleton] at hn
  rw [hmove n (by omega) hne]
  have hlen : ¬ ((prefixOf x n).length = p.length) := by
    simp only [length_prefixOf]; omega
  simp only [if_neg hlen]

/-- If Player I has no winning strategy from a position `p`, then there is a move `a` after
which Player I still has no winning strategy.  (Used at the positions where it is Player II's
turn: this is the move Player II will play.) -/
