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

lemma finrank_piSub [Fintype X] [Fintype Z] (W : Submodule ℂ (X → ℂ)) :
    finrank ℂ (piSub (X := X) Z W) = Fintype.card Z * finrank ℂ W := by
  rw [(piSubEquiv W).finrank_eq]
  simp [Module.finrank_pi_fintype]

/-- Moving an index from the rows to the columns can decrease the rank at most by the
factor `Fintype.card Z`. -/
