/-
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- Pigeonhole on five vertices two-coloured: three of them get the same colour. -/
lemma exists_three_same_color (f : Fin 5 → Bool) :
    ∃ x y z : Fin 5, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ f x = f y ∧ f y = f z := by
  revert f; decide

/-- Any 2-colouring of the edges of `K₆` contains a monochromatic triangle.  (Symmetry of `c`
is not needed here: the triangle produced is always oriented consistently, so the statement
holds for an arbitrary `Bool`-valued function on ordered pairs.) -/
lemma exists_mono_triangle_six (c : Fin 6 → Fin 6 → Bool) :
    ∃ a b d : Fin 6, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ c a b = c a d ∧ c a b = c b d := by
  obtain ⟨x, y, z, hxy, hxz, hyz, h1, h2⟩ := exists_three_same_color (fun i => c 0 i.succ)
  set X : Fin 6 := x.succ
  set Y : Fin 6 := y.succ
  set Z : Fin 6 := z.succ
  have hXY : X ≠ Y := fun h => hxy (Fin.succ_injective _ h)
  have hXZ : X ≠ Z := fun h => hxz (Fin.succ_injective _ h)
  have hYZ : Y ≠ Z := fun h => hyz (Fin.succ_injective _ h)
  have hX0 : (0 : Fin 6) ≠ X := (Fin.succ_ne_zero x).symm
  have hY0 : (0 : Fin 6) ≠ Y := (Fin.succ_ne_zero y).symm
  have hZ0 : (0 : Fin 6) ≠ Z := (Fin.succ_ne_zero z).symm
  by_cases hxy' : c X Y = c 0 X
  · exact ⟨0, X, Y, hX0, hY0, hXY, h1, hxy'.symm⟩
  by_cases hxz' : c X Z = c 0 X
  · exact ⟨0, X, Z, hX0, hZ0, hXZ, h1.trans h2, hxz'.symm⟩
  by_cases hyz' : c Y Z = c 0 X
  · exact ⟨0, Y, Z, hY0, hZ0, hYZ, h2, (hyz'.trans h1).symm⟩
  · have key : ∀ a b k : Bool, a ≠ k → b ≠ k → a = b := by decide
    exact ⟨X, Y, Z, hXY, hXZ, hYZ, key _ _ _ hxy' hxz', key _ _ _ hxy' hyz'⟩

/-- The 5-cycle colouring of the edges of `K₅`: an edge is `true` iff its endpoints are
consecutive modulo `5`. -/
def cycleColoring : Fin 5 → Fin 5 → Bool := fun i j => decide (i - j = 1 ∨ i - j = 4)

/-- **R(3,3) = 6**: every 2-colouring of the edges of `K₆` contains a monochromatic
triangle, while `K₅` admits a 2-colouring with no monochromatic triangle. -/
theorem ramsey_3_3 :
    (∀ c : Fin 6 → Fin 6 → Bool, (∀ i j, c i j = c j i) →
      ∃ a b d : Fin 6, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ c a b = c a d ∧ c a b = c b d) ∧
    (∃ c : Fin 5 → Fin 5 → Bool, (∀ i j, c i j = c j i) ∧
      ∀ a b d : Fin 5, a ≠ b → a ≠ d → b ≠ d → ¬(c a b = c a d ∧ c a b = c b d)) := by
  refine ⟨fun c _ => exists_mono_triangle_six c, cycleColoring, ?_, ?_⟩ <;> decide

end Math

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

