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

lemma exists_prefix_subset_of_isOpen [TopologicalSpace A] {W : Set (ℕ → A)} (hW : IsOpen W)
    {x : ℕ → A} (hx : x ∈ W) : ∃ n : ℕ, ∀ y : ℕ → A, (∀ i, i < n → y i = x i) → y ∈ W := by
  rw [isOpen_pi_iff] at hW
  obtain ⟨I, u, hu, hsub⟩ := hW x hx
  refine ⟨I.sup id + 1, fun y hy => hsub ?_⟩
  intro i hi
  have hmem : i ∈ I := Finset.mem_coe.mp hi
  have hle : i ≤ I.sup id := Finset.le_sup (f := id) hmem
  rw [hy i (by omega)]
  exact (hu i hmem).2

/-- **Gale–Stewart theorem**: every open game is determined.

Two players alternately choose elements of a nonempty set `A` of moves, Player I moving at the
even stages and Player II at the odd stages, producing a play `x : ℕ → A`.  Player I wins if
`x ∈ W`.  If the payoff set `W` is open in the product topology on `ℕ → A` (with `A` discrete),
then one of the two players has a winning strategy from the initial (empty) position. -/
