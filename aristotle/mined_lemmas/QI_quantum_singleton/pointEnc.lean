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

def pointEnc (q n : ℕ) (hq : 0 < q) : Matrix (Fin n → Fin q) (Fin 1) ℂ :=
  fun x _ => if x = (fun _ => (⟨0, hq⟩ : Fin q)) then 1 else 0

