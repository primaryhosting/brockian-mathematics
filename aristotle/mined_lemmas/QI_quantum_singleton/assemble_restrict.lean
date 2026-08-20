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

lemma assemble_restrict (SA SB : Finset (Fin n)) (a : SA → Fin q) (b : SB → Fin q)
    (c : {i : Fin n // i ∉ SA ∪ SB} → Fin q) :
    (fun i : SA => assemble SA SB a b c i) = a := by
  funext i; simp [assemble, i.2]

