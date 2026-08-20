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

lemma assemble_restrict_B (SA SB : Finset (Fin n)) (hd : Disjoint SA SB) (a : SA → Fin q)
    (b : SB → Fin q) (c : {i : Fin n // i ∉ SA ∪ SB} → Fin q) :
    (fun i : SB => assemble SA SB a b c i) = b := by
  funext i
  have hi : (i : Fin n) ∉ SA := Finset.disjoint_right.mp hd i.2
  simp [assemble, hi, i.2]

