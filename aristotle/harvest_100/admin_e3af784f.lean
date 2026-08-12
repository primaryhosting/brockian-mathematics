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

/-- `MonoTriangle c i j k` says that the three distinct vertices `i, j, k` span a
triangle all of whose edges get the same colour under the edge-colouring `c`. -/
abbrev MonoTriangle {n : ℕ} (c : Fin n → Fin n → Bool) (i j k : Fin n) : Prop :=
  i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ c i j = c j k ∧ c i j = c i k

/-- Among five booleans, three of them (at distinct, increasing indices) are equal. -/
lemma three_eq_of_five (b : Fin 5 → Bool) :
    ∃ i j k : Fin 5, i < j ∧ j < k ∧ b i = b j ∧ b j = b k := by
  revert b; decide

/-- Every 2-colouring of the edges of `K₆` contains a monochromatic triangle.
(No symmetry assumption on `c` is needed here: the triangle produced only uses
edges read in one fixed orientation.) -/
lemma exists_mono_triangle_six (c : Fin 6 → Fin 6 → Bool) :
    ∃ i j k, MonoTriangle c i j k := by
  obtain ⟨i, j, k, hij, hjk, h1, h2⟩ := three_eq_of_five (fun i : Fin 5 => c 0 i.succ)
  set x : Fin 6 := i.succ with hx
  set y : Fin 6 := j.succ with hy
  set z : Fin 6 := k.succ with hz
  have hxy : x ≠ y := fun h => absurd (Fin.succ_injective _ h) (ne_of_lt hij)
  have hyz : y ≠ z := fun h => absurd (Fin.succ_injective _ h) (ne_of_lt hjk)
  have hxz : x ≠ z := fun h =>
    absurd (Fin.succ_injective _ h) (ne_of_lt (lt_trans hij hjk))
  have hx0 : (0 : Fin 6) ≠ x := (Fin.succ_ne_zero i).symm
  have hy0 : (0 : Fin 6) ≠ y := (Fin.succ_ne_zero j).symm
  have hz0 : (0 : Fin 6) ≠ z := (Fin.succ_ne_zero k).symm
  by_cases hcxy : c x y = c 0 x
  · exact ⟨0, x, y, hx0, hy0, hxy, hcxy.symm, h1⟩
  · by_cases hcyz : c y z = c 0 y
    · exact ⟨0, y, z, hy0, hz0, hyz, hcyz.symm, h2⟩
    · by_cases hcxz : c x z = c 0 x
      · exact ⟨0, x, z, hx0, hz0, hxz, hcxz.symm, h1.trans h2⟩
      · refine ⟨x, y, z, hxy, hxz, hyz, ?_, ?_⟩
        · rw [Bool.eq_not_of_ne hcxy, Bool.eq_not_of_ne hcyz, h1]
        · rw [Bool.eq_not_of_ne hcxy, Bool.eq_not_of_ne hcxz]

/-- The pentagon colouring of `K₅`: an edge is `true` exactly when its endpoints are
consecutive modulo 5. -/
def pentagon (i j : Fin 5) : Bool :=
  decide ((i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val)

/-- **Ramsey's theorem `R(3,3) = 6`.**  Every 2-colouring of the edges of `K₆` has a
monochromatic triangle, while `K₅` admits a 2-colouring with none. -/
theorem ramsey_3_3 :
    (∀ c : Fin 6 → Fin 6 → Bool, (∀ i j, c i j = c j i) →
        ∃ i j k, MonoTriangle c i j k) ∧
    (∃ c : Fin 5 → Fin 5 → Bool, (∀ i j, c i j = c j i) ∧
        ∀ i j k, ¬ MonoTriangle c i j k) := by
  refine ⟨fun c _ => exists_mono_triangle_six c, pentagon, ?_, ?_⟩
  · decide
  · decide

end Math

#print axioms Math.ramsey_3_3

