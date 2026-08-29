/-!
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- An auxiliary "vector" of five booleans, read off as a function on `Fin 6` (the value at
the index `0` is irrelevant and set to `false`). -/
private def boolVec (b1 b2 b3 b4 b5 : Bool) : Fin 6 → Bool
  | 0 => false
  | 1 => b1
  | 2 => b2
  | 3 => b3
  | 4 => b4
  | 5 => b5

/-- Pigeonhole principle: among the five booleans `b1, …, b5` there are three, at strictly
increasing indices, that are equal. -/
private theorem exists_three_equal (b1 b2 b3 b4 b5 : Bool) :
    ∃ x y z : Fin 6, 0 < x ∧ x < y ∧ y < z ∧
      boolVec b1 b2 b3 b4 b5 x = boolVec b1 b2 b3 b4 b5 y ∧
      boolVec b1 b2 b3 b4 b5 y = boolVec b1 b2 b3 b4 b5 z := by
  revert b1 b2 b3 b4 b5; decide

private theorem boolVec_colour (c : Fin 6 → Fin 6 → Bool) (x : Fin 6) (hx : x ≠ 0) :
    boolVec (c 0 1) (c 0 2) (c 0 3) (c 0 4) (c 0 5) x = c 0 x := by
  match x with
  | 0 => exact absurd rfl hx
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl

/-- Any 2-colouring of the edges of `K₆` contains a monochromatic triangle. -/
private theorem mono_triangle_of_six (c : Fin 6 → Fin 6 → Bool) :
    ∃ a b d : Fin 6, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ c a b = c a d ∧ c a b = c b d := by
  obtain ⟨x, y, z, h0x, hxy₀, hyz₀, e1, e2⟩ :=
    exists_three_equal (c 0 1) (c 0 2) (c 0 3) (c 0 4) (c 0 5)
  have hx0 : x ≠ 0 := (Fin.ne_of_lt h0x).symm
  have hy0 : y ≠ 0 := (Fin.ne_of_lt (Nat.lt_trans h0x hxy₀)).symm
  have hz0 : z ≠ 0 := (Fin.ne_of_lt (Nat.lt_trans h0x (Nat.lt_trans hxy₀ hyz₀))).symm
  have hxy : x ≠ y := Fin.ne_of_lt hxy₀
  have hyz : y ≠ z := Fin.ne_of_lt hyz₀
  have hxz : x ≠ z := Fin.ne_of_lt (Nat.lt_trans hxy₀ hyz₀)
  rw [boolVec_colour c x hx0, boolVec_colour c y hy0] at e1
  rw [boolVec_colour c y hy0, boolVec_colour c z hz0] at e2
  by_cases hxy' : c x y = c 0 x
  · exact ⟨0, x, y, fun h => hx0 h.symm, fun h => hy0 h.symm, hxy, e1, hxy'.symm⟩
  · by_cases hxz' : c x z = c 0 x
    · exact ⟨0, x, z, fun h => hx0 h.symm, fun h => hz0 h.symm, hxz, e1.trans e2, hxz'.symm⟩
    · by_cases hyz' : c y z = c 0 y
      · exact ⟨0, y, z, fun h => hy0 h.symm, fun h => hz0 h.symm, hyz, e2, hyz'.symm⟩
      · refine ⟨x, y, z, hxy, hxz, hyz, ?_, ?_⟩
        · revert hxy' hxz'; cases c x y <;> cases c x z <;> cases c 0 x <;> simp
        · rw [← e1] at hyz'
          revert hxy' hyz'; cases c x y <;> cases c y z <;> cases c 0 x <;> simp

/-- The "pentagon" colouring of the edges of `K₅`: an edge is coloured `true` exactly when its
endpoints are adjacent in the 5-cycle `0 - 1 - 2 - 3 - 4 - 0`, and `false` otherwise. -/
private def pentagon (i j : Fin 5) : Bool :=
  decide ((i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val)

/-- **R(3,3) = 6.**

A 2-colouring of the edges of a complete graph is modelled as a symmetric `Bool`-valued
function on pairs of vertices, and a monochromatic triangle is a triple of pairwise distinct
vertices all three of whose connecting edges receive the same colour.

The first conjunct states that every 2-colouring of the edges of `K₆` contains a
monochromatic triangle (note that the symmetry hypothesis, which is part of the notion of an
edge colouring, turns out not to be needed for this direction). The second conjunct exhibits
a 2-colouring of the edges of `K₅` — the pentagon colouring — with no monochromatic
triangle. -/
theorem ramsey_3_3 :
    (∀ c : Fin 6 → Fin 6 → Bool, (∀ i j, c i j = c j i) →
        ∃ a b d : Fin 6, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ c a b = c a d ∧ c a b = c b d) ∧
    (∃ c : Fin 5 → Fin 5 → Bool, (∀ i j, c i j = c j i) ∧
        ∀ a b d : Fin 5, a ≠ b → a ≠ d → b ≠ d → ¬(c a b = c a d ∧ c a b = c b d)) := by
  refine ⟨fun c _ => mono_triangle_of_six c, pentagon, by decide, by decide⟩

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

