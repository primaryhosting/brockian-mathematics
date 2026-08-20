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

def splitEquiv (SA SB : Finset (Fin n)) (hd : Disjoint SA SB) :
    (Fin n → Fin q) ≃ (SA → Fin q) × (SB → Fin q) × ({i : Fin n // i ∉ SA ∪ SB} → Fin q) where
  toFun x := (fun i => x i, fun i => x i, fun i => x i)
  invFun p := assemble SA SB p.1 p.2.1 p.2.2
  left_inv x := by
    funext i
    simp only [assemble]
    split <;> [skip; split] <;> rfl
  right_inv p := by
    obtain ⟨a, b, c⟩ := p
    have hb : ∀ i : SB, (i : Fin n) ∉ SA := fun i hi => Finset.disjoint_left.mp hd hi i.2
    ext i <;> simp only [assemble]
    · simp [i.2]
    · simp [hb i, i.2]
    · have h1 : (i : Fin n) ∉ SA := fun h => i.2 (Finset.mem_union_left _ h)
      have h2 : (i : Fin n) ∉ SB := fun h => i.2 (Finset.mem_union_right _ h)
      simp [h1, h2]

