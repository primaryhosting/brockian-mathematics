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

namespace Chem

open Polynomial Complex

instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- The cycle graph `C₁₃`, on the vertex set `ZMod 13`, where `i` and `j` are adjacent
iff they differ by `1`. -/

lemma adj_iff (i j : ZMod 13) : C13.Adj i j ↔ (j = i + 1 ∨ j = i - 1) := by
  have hne : ∀ a : ZMod 13, a ≠ a + 1 := by decide
  have hne' : ∀ a : ZMod 13, a ≠ a - 1 := by decide
  rw [C13, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact Or.inl h
    · exact Or.inr (by rw [h]; ring)
  · rintro (h | h) <;> subst h
    · exact ⟨hne i, Or.inl rfl⟩
    · exact ⟨hne' i, Or.inr (by ring)⟩

