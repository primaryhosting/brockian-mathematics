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

lemma exists_noWinI_of_moveII [Nonempty A] {p : List A}
    (h : ¬ ∃ σ : List A → A, WinningI W σ p) :
    ∃ a : A, ¬ ∃ σ : List A → A, WinningI W σ (p ++ [a]) := by
  by_contra hcon
  push_neg at hcon
  choose f hf using hcon
  refine h ⟨fun q => if hq : p.length < q.length then f q[p.length] q else Classical.arbitrary A,
    ?_⟩
  intro x hx
  obtain ⟨hext, hmove⟩ := hx
  refine hf (x p.length) x ⟨extends_append_singleton hext rfl, ?_⟩
  intro n hn hne
  simp only [List.length_append, List.length_singleton] at hn
  rw [hmove n (by omega) hne]
  have hlt : p.length < (prefixOf x n).length := by
    simp only [length_prefixOf]; omega
  simp only [dif_pos hlt, getElem_prefixOf]

end NoWin

/-- Openness of `W` in the product topology, in combinatorial form: every play in `W` has a
finite prefix all of whose extensions lie in `W`. -/
