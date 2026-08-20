/-
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math

/-- Pigeonhole: among five Booleans, three are equal. -/
private lemma pigeon_five (f : Fin 5 → Bool) :
    ∃ a b d : Fin 5, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ f a = f b ∧ f a = f d := by
  revert f
  decide

/-- The pentagon colouring of `K₅`: an edge is `true` iff its endpoints are
consecutive modulo `5`. -/
private def pentagon (i j : Fin 5) : Bool :=
  decide ((i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val)

/-- **R(3,3) = 6.**  Every symmetric 2-colouring of the edges of `K₆` contains a
monochromatic triangle, while `K₅` admits a symmetric 2-colouring with none.

The symmetry hypothesis in the first part is part of the notion of an edge
colouring, but the proof given here does not actually need it. -/
theorem ramsey_3_3 :
    (∀ c : Fin 6 → Fin 6 → Bool, (∀ i j, c i j = c j i) →
      ∃ x y z : Fin 6, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ c x y = c x z ∧ c x y = c y z) ∧
    (∃ c : Fin 5 → Fin 5 → Bool, (∀ i j, c i j = c j i) ∧
      ∀ x y z : Fin 5, x ≠ y → x ≠ z → y ≠ z →
        ¬ (c x y = c x z ∧ c x y = c y z)) := by
  constructor
  · intro c hsym
    obtain ⟨a, b, d, hab, had, hbd, h1, h2⟩ := pigeon_five (fun i => c 0 i.succ)
    have hAB : a.succ ≠ b.succ := fun h => hab (Fin.succ_injective _ h)
    have hAD : a.succ ≠ d.succ := fun h => had (Fin.succ_injective _ h)
    have hBD : b.succ ≠ d.succ := fun h => hbd (Fin.succ_injective _ h)
    have hA0 : (0 : Fin 6) ≠ a.succ := (Fin.succ_ne_zero a).symm
    have hB0 : (0 : Fin 6) ≠ b.succ := (Fin.succ_ne_zero b).symm
    have hD0 : (0 : Fin 6) ≠ d.succ := (Fin.succ_ne_zero d).symm
    by_cases e1 : c a.succ b.succ = c 0 a.succ
    · exact ⟨0, a.succ, b.succ, hA0, hB0, hAB, h1, e1.symm⟩
    by_cases e2 : c a.succ d.succ = c 0 a.succ
    · exact ⟨0, a.succ, d.succ, hA0, hD0, hAD, h2, e2.symm⟩
    by_cases e3 : c b.succ d.succ = c 0 b.succ
    · exact ⟨0, b.succ, d.succ, hB0, hD0, hBD, h1.symm.trans h2, e3.symm⟩
    · refine ⟨a.succ, b.succ, d.succ, hAB, hAD, hBD, ?_, ?_⟩
      · revert e1 e2
        cases c a.succ b.succ <;> cases c a.succ d.succ <;> cases c 0 a.succ <;> simp
      · rw [← h1] at e3
        revert e1 e3
        cases c a.succ b.succ <;> cases c b.succ d.succ <;> cases c 0 a.succ <;> simp
  · refine ⟨pentagon, ?_, ?_⟩
    · decide
    · decide

end Math

