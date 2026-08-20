import Mathlib

open Finset

namespace Math

/-- Every primitive 8-th root of unity `ζ` in `ℂ` satisfies `ζ ^ 4 = -1`. -/

lemma pow_four_eq_neg_one_of_mem_primitiveRoots_eight
    {ζ : ℂ} (hζ : ζ ∈ primitiveRoots 8 ℂ) : ζ ^ 4 = -1 := by
  rw [mem_primitiveRoots (by norm_num)] at hζ
  have h8 : ζ ^ 8 = 1 := hζ.pow_eq_one
  have h4 : ζ ^ 4 ≠ 1 := by
    intro h
    have := (hζ.pow_eq_one_iff_dvd 4).1 h
    omega
  have hsq : (ζ ^ 4 - 1) * (ζ ^ 4 + 1) = 0 := by linear_combination h8
  rcases mul_eq_zero.1 hsq with h | h
  · exact absurd (sub_eq_zero.1 h) h4
  · linear_combination h

/-- The Möbius function vanishes at `8`, since `8 = 2 ^ 3` is not squarefree. -/
