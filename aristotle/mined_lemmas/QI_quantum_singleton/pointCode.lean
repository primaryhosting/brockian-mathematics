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

def pointCode (q n d : ℕ) (hq : 0 < q) : QCode q n 1 d where
  enc := pointEnc q n hq
  isometry := pointEnc_isometry q n hq
  detects := by
    intro S _ O
    refine ⟨((pointEnc q n hq)ᴴ * extendOp S O * pointEnc q n hq) 0 0, ?_⟩
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simp

/-- The hypothesis `1 ≤ k` in `quantum_singleton` cannot be dropped: the one-dimensional code
on a single qubit has distance at least `2`, and `0 + 2 * (2 - 1) ≤ 1` is false. -/
