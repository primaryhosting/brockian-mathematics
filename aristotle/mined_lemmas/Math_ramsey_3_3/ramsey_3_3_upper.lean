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

namespace Math

/-- Pigeonhole: any 2-coloring of five items has three items of the same colour. -/

theorem ramsey_3_3_upper (c : Fin 6 → Fin 6 → Bool) :
    ∃ a b d : Fin 6, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ c a b = c a d ∧ c a d = c b d := by
  obtain ⟨i, j, k, hij, hjk, h1, h2⟩ := three_same_of_five (fun i => c 0 i.succ)
  set A := i.succ with hA
  set B := j.succ with hB
  set C := k.succ with hC
  have hAB : A ≠ B := fun h => absurd (Fin.succ_injective _ h) (ne_of_lt hij)
  have hBC : B ≠ C := fun h => absurd (Fin.succ_injective _ h) (ne_of_lt hjk)
  have hAC : A ≠ C := fun h =>
    absurd (Fin.succ_injective _ h) (ne_of_lt (lt_trans hij hjk))
  have h0A : (0 : Fin 6) ≠ A := (Fin.succ_ne_zero i).symm
  have h0B : (0 : Fin 6) ≠ B := (Fin.succ_ne_zero j).symm
  have h0C : (0 : Fin 6) ≠ C := (Fin.succ_ne_zero k).symm
  by_cases e1 : c A B = c 0 A
  · exact ⟨0, A, B, h0A, h0B, hAB, h1, by rw [← h1, ← e1]⟩
  by_cases e2 : c A C = c 0 A
  · exact ⟨0, A, C, h0A, h0C, hAC, h1.trans h2, by rw [← h1.trans h2, ← e2]⟩
  by_cases e3 : c B C = c 0 A
  · exact ⟨0, B, C, h0B, h0C, hBC, h2, (e3.trans (h1.trans h2)).symm⟩
  · refine ⟨A, B, C, hAB, hAC, hBC, ?_, ?_⟩
    · rw [Bool.eq_iff_iff]; revert e1 e2; cases c A B <;> cases c A C <;> cases c 0 A <;> simp
    · rw [Bool.eq_iff_iff]; revert e2 e3; cases c B C <;> cases c A C <;> cases c 0 A <;> simp

/-- **R(3,3) = 6**: every 2-colouring of the edges of `K₆` has a monochromatic triangle,
while `K₅` admits a 2-colouring with no monochromatic triangle. -/
