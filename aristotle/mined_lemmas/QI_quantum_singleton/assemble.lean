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

def assemble (SA SB : Finset (Fin n)) (a : SA → Fin q) (b : SB → Fin q)
    (c : {i : Fin n // i ∉ SA ∪ SB} → Fin q) : Fin n → Fin q :=
  fun i => if h : i ∈ SA then a ⟨i, h⟩ else if h' : i ∈ SB then b ⟨i, h'⟩ else
    c ⟨i, by simp [h, h']⟩

/-- Splitting the qudits into the three groups `SA`, `SB` and the rest. -/
