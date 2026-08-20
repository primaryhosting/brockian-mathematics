import Mathlib

/-!
# Abstract machinery for paradoxical decompositions

This file develops the general theory needed for the Banach–Tarski paradox, on top of
Mathlib's `Equidecomp` (equidecompositions for a group action).
-/

open Set Function Pointwise

namespace BT

variable {X G H : Type*} [Nonempty X] [Group G] [MulAction G X]

/-- Build an equidecomposition out of a function which is a bijection from `A` to `B` and
moves every point of `A` by an element of a fixed finite set of group elements. -/

lemma matOf_mulVec (x : Fin 2 × Bool) (v : ℤ × ℤ × ℤ) :
    matOf x *ᵥ ![(v.1 : ℝ), (v.2.1 : ℝ) * Real.sqrt 2, (v.2.2 : ℝ)] =
      (3 : ℝ)⁻¹ • ![((istep x v).1 : ℝ), ((istep x v).2.1 : ℝ) * Real.sqrt 2,
        ((istep x v).2.2 : ℝ)] := by
  have h3 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  obtain ⟨p, q, r⟩ := v
  rcases x with ⟨i, b⟩
  fin_cases i <;> cases b <;>
    (ext k; fin_cases k <;>
      simp [matOf, genMat, rA, rB, istep, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
      ring_nf; rw [h3]; ring)

/-- The image of `(0, √2, 0)` under the word `L`. -/
