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

lemma assemble_agree_off (SA SB : Finset (Fin n)) (hd : Disjoint SA SB)
    (a a' : SA → Fin q) (b b' : SB → Fin q)
    (c c' : {i : Fin n // i ∉ SA ∪ SB} → Fin q) :
    (∀ i, i ∉ SA → assemble SA SB a b c i = assemble SA SB a' b' c' i) ↔ (b = b' ∧ c = c') := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · funext i
      have hi : (i : Fin n) ∉ SA := Finset.disjoint_right.mp hd i.2
      simpa [assemble, hi, i.2] using h i hi
    · funext i
      have h1 : (i : Fin n) ∉ SA := fun hx => i.2 (Finset.mem_union_left _ hx)
      have h2 : (i : Fin n) ∉ SB := fun hx => i.2 (Finset.mem_union_right _ hx)
      simpa [assemble, h1, h2] using h i h1
  · rintro ⟨rfl, rfl⟩ i hi
    simp [assemble, hi]

/-- An operator acting on the qudits in `S` only, extended by the identity to all `n` qudits. -/
