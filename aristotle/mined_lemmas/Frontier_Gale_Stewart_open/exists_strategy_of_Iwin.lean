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

lemma exists_strategy_of_Iwin (p : List A) (h : Iwin W p) :
    ∃ σ : List A → A, ∀ s : List A → A,
      (∀ n, Even n → p.length ≤ n → s (prefixOf (play s) n) = σ (prefixOf (play s) n)) →
      prefixOf (play s) p.length = p → play s ∈ W := by
  classical
  induction h with
  | base p hb =>
      exact ⟨fun _ => Classical.arbitrary A, fun s _ hpref => hb _ hpref⟩
  | stepI p a hev _ ih =>
      obtain ⟨σ', hσ'⟩ := ih
      refine ⟨fun q => if q = p then a else σ' q, ?_⟩
      intro s hagree hpref
      have hxp : play s p.length = a := by
        rw [play_eq, hpref]
        have h2 := hagree p.length hev le_rfl
        rw [hpref] at h2
        simpa using h2
      have hpref' : prefixOf (play s) (p ++ [a]).length = p ++ [a] := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        rw [show p.length + (0 + 1) = p.length + 1 by ring, prefixOf_succ, hpref, hxp]
      refine hσ' s ?_ hpref'
      intro n hn hle
      simp only [List.length_append, List.length_cons, List.length_nil] at hle
      have hlt : p.length < n := by omega
      have hne : prefixOf (play s) n ≠ p := by
        intro hc
        have h3 := congrArg List.length hc
        simp at h3
        omega
      have h4 := hagree n hn (le_of_lt hlt)
      simpa [hne] using h4
  | stepII p hodd _ ih =>
      choose f hf using ih
      refine ⟨fun q => if hq : p.length < q.length then f (q[p.length]) q
        else Classical.arbitrary A, ?_⟩
      intro s hagree hpref
      set a := play s p.length with ha
      have hpref' : prefixOf (play s) (p ++ [a]).length = p ++ [a] := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        rw [show p.length + (0 + 1) = p.length + 1 by ring, prefixOf_succ, hpref]
      refine hf a s ?_ hpref'
      intro n hn hle
      simp only [List.length_append, List.length_cons, List.length_nil] at hle
      have hlt : p.length < n := by omega
      have hlt' : p.length < (prefixOf (play s) n).length := by simpa using hlt
      have h5 := hagree n hn (le_of_lt hlt)
      rw [h5]
      simp only [dif_pos hlt', getElem_prefixOf, ha]

/-- If player I cannot force `W` from the empty position, player II has a strategy which
avoids all positions from which player I can force `W`. -/
