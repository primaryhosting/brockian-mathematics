import Mathlib

/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

universe u

variable {A : Type u}

/-! ## The game framework

We consider infinite two–player games on a set `A` of moves.  A *play* is a sequence
`x : ℕ → A`; player `0` chooses the moves `x n` with `n` even, player `1` chooses the moves
`x n` with `n` odd.  A *strategy* is a function `List A → A` assigning a move to every finite
position (the player only consults it at their own turns). -/

/-- The length-`n` initial segment of a play. -/

theorem Borel_determinacy
    (hUnion : ∀ f : ℕ → Set (ℕ → A), (∀ n, IsBorelSet (f n)) →
      (∀ n, BiDetermined (f n)) → BiDetermined (⋃ n, f n))
    {S : Set (ℕ → A)} (hS : IsBorelSet S) : Determined S := by
  have hgen : ∀ t : Set (ℕ → A),
      MeasurableSpace.GenerateMeasurable {u : Set (ℕ → A) | IsClosed u} t → IsBorelSet t := by
    intro t ht
    show @MeasurableSet (ℕ → A) (borel (ℕ → A)) t
    rw [borel_eq_generateFrom_isClosed]
    exact ht
  have key : ∀ t : Set (ℕ → A),
      MeasurableSpace.GenerateMeasurable {u : Set (ℕ → A) | IsClosed u} t → BiDetermined t := by
    intro t ht
    induction ht with
    | basic u hu => exact closed_biDetermined hu
    | empty => exact closed_biDetermined isClosed_empty
    | compl t _ ih => exact ih.compl
    | iUnion f hf ih => exact hUnion f (fun n => hgen _ (hf n)) ih
  have hS' : MeasurableSpace.GenerateMeasurable {u : Set (ℕ → A) | IsClosed u} S := by
    have h := hS
    rw [IsBorelSet, borel_eq_generateFrom_isClosed] at h
    exact h
  exact (key S hS').1

end Borel

end Frontier

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

