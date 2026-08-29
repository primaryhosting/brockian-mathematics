import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Filter Asymptotics
open Fintype (card)

namespace Math2

variable {n : ℕ}

/-- A *cap set* in `𝔽₃ⁿ`: a set containing no three (not necessarily distinct) points on a line,
i.e. whenever `x + y + z = 0` for `x, y, z` in the set, the three points coincide.

Since `3 • v = 0` in `𝔽₃ⁿ`, the condition `x + y + z = 0` says exactly that `x, y, z` form a
three-term arithmetic progression, so this is equivalent to `ThreeAPFree`. -/

theorem exists_capSet_card_eq (n : ℕ) :
    ∃ A : Finset (Fin n → ZMod 3), IsCapSet (A : Set (Fin n → ZMod 3)) ∧
      #A = capSetNumber n := by
  classical
  have hne : (((Finset.univ : Finset (Finset (Fin n → ZMod 3))).filter
      fun A => ThreeAPFree (A : Set (Fin n → ZMod 3)))).Nonempty :=
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [threeAPFree_empty]⟩⟩
  obtain ⟨A, hA, hAcard⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  refine ⟨A, ?_, ?_⟩
  · exact (isCapSet_iff_threeAPFree _).2 (Finset.mem_filter.1 hA).2
  · rw [capSetNumber, ← hAcard]

