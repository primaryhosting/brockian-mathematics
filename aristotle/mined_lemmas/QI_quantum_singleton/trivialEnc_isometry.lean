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

lemma trivialEnc_isometry (q n : ℕ) : (trivialEnc q n)ᴴ * trivialEnc q n = 1 := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  simp only [trivialEnc, Matrix.conjTranspose_apply, RCLike.star_def,
    apply_ite (starRingEnd ℂ), map_one, map_zero, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (finFunctionFinEquiv.symm i)]
  by_cases h : i = j
  · subst h; simp
  · have hne : ¬ (finFunctionFinEquiv.symm i = finFunctionFinEquiv.symm j) :=
      fun hx => h (finFunctionFinEquiv.symm.injective hx)
    simp [h, hne]

/-- The trivial (unencoded) code `[[n, n, 1]]_q`, which shows that the definition of `QCode`
is satisfiable; the bound then reads `n + 2 * 0 ≤ n`. -/
