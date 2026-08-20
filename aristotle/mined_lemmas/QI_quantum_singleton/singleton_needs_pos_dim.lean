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

theorem singleton_needs_pos_dim : ∃ _Q : QCode 2 1 (2 ^ 0) 2, ¬ (0 + 2 * (2 - 1) ≤ 1) :=
  ⟨pointCode 2 1 2 (by norm_num), by decide⟩

end QI

