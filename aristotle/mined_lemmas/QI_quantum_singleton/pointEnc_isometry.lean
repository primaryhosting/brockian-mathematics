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

lemma pointEnc_isometry (q n : ℕ) (hq : 0 < q) :
    (pointEnc q n hq)ᴴ * pointEnc q n hq = 1 := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  simp only [pointEnc, Matrix.conjTranspose_apply, RCLike.star_def, apply_ite (starRingEnd ℂ),
    map_one, map_zero, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (fun _ => (⟨0, hq⟩ : Fin q))]
  simp [Matrix.one_apply, Subsingleton.elim i j]

/-- A one-dimensional code space (`K = 1`, i.e. `k = 0`) satisfies the Knill–Laflamme
condition for errors of *every* weight. -/
