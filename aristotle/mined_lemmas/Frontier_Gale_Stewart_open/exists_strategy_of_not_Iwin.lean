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

/-- The list of the first `n` moves of the infinite play `x`. -/

lemma exists_strategy_of_not_Iwin (h : ¬ Iwin W []) :
    ∃ τ : List A → A, ∀ σ : List A → A, ∀ n : ℕ,
      ¬ Iwin W (prefixOf (play (combine σ τ)) n) := by
  classical
  refine ⟨fun p => if hp : ∃ a, ¬ Iwin W (p ++ [a]) then Classical.choose hp
    else Classical.arbitrary A, ?_⟩
  set τ : List A → A := fun p => if hp : ∃ a, ¬ Iwin W (p ++ [a]) then Classical.choose hp
    else Classical.arbitrary A with hτdef
  intro σ n
  induction n with
  | zero => simpa [prefixOf] using h
  | succ n ih =>
      rw [prefixOf_succ]
      intro hcon
      set x := play (combine σ τ) with hx
      set p := prefixOf x n with hp
      have hlen : p.length = n := by simp [hp]
      by_cases he : Even n
      · exact ih (Iwin.stepI p (x n) (by rw [hlen]; exact he) hcon)
      · have hxn : x n = τ p := by
          rw [hx, play_eq]
          simp only [combine, ← hp, ← hx]
          rw [if_neg (by rw [hlen]; exact he)]
        have hex : ∃ a, ¬ Iwin W (p ++ [a]) := by
          by_contra hall
          push_neg at hall
          exact ih (Iwin.stepII p (by rw [hlen]; exact he) hall)
        have hchoice : τ p = Classical.choose hex := by
          rw [hτdef]; simp only [dif_pos hex]
        rw [hxn, hchoice] at hcon
        exact Classical.choose_spec hex hcon

end

/-- Openness of `W` in the product topology of the discrete space `A`: every play in `W`
has a finite prefix all of whose extensions lie in `W`. -/
