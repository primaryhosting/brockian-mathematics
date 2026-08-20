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

def trivialCode (q n : ℕ) : QCode q n (q ^ n) 1 where
  enc := trivialEnc q n
  isometry := trivialEnc_isometry q n
  detects := by
    classical
    intro S hS O
    obtain rfl : S = ∅ := Finset.card_eq_zero.mp (by omega)
    refine ⟨O (fun i => (Finset.notMem_empty _ i.2).elim)
      (fun i => (Finset.notMem_empty _ i.2).elim), ?_⟩
    rw [extendOp_empty O (fun i => (Finset.notMem_empty _ i.2).elim), Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, trivialEnc_isometry]

/-- The encoding into a fixed basis state, i.e. a one-dimensional code space. -/
