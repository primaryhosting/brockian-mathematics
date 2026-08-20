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

def piSub (Z : Type*) [Fintype X] (W : Submodule ℂ (X → ℂ)) : Submodule ℂ (Z × X → ℂ) where
  carrier := {v | ∀ z, (fun x => v (z, x)) ∈ W}
  add_mem' := by intro a b ha hb z; exact W.add_mem (ha z) (hb z)
  zero_mem' := fun z => W.zero_mem
  smul_mem' := by intro c a ha z; exact W.smul_mem c (ha z)

/-- `piSub Z W` is linearly isomorphic to `Z → W`. -/
