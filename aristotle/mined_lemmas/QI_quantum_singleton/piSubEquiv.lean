import Mathlib

/-!
Rank tools and the core decoupling lemma behind the quantum Singleton bound.
-/

open Matrix Module
open scoped ComplexOrder

namespace QI

variable {X Y Z R : Type*}

section RankTools

/-- Vectors on `Z × X` all of whose `Z`-slices lie in `W`. -/

noncomputable def piSubEquiv [Fintype X] (W : Submodule ℂ (X → ℂ)) :
    piSub (X := X) Z W ≃ₗ[ℂ] (Z → W) where
  toFun v := fun z => ⟨fun x => v.1 (z, x), v.2 z⟩
  map_add' := by intro a b; rfl
  map_smul' := by intro c a; rfl
  invFun g := ⟨fun p => (g p.1).1 p.2, fun z => (g z).2⟩
  left_inv := by intro v; ext p; rfl
  right_inv := by intro g; ext z x; rfl

