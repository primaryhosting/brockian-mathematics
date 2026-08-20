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

def trivialEnc (q n : ℕ) : Matrix (Fin n → Fin q) (Fin (q ^ n)) ℂ :=
  fun x i => if x = finFunctionFinEquiv.symm i then 1 else 0

