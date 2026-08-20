import RequestProject.PentagonExt

/-!
# Decomposition of the vertex representation of a regular `n`-gon, `n` odd

For an odd number of vertices `n = 2m+1`, the permutation character of `DihedralGroup n`
acting on the vertices of the regular `n`-gon decomposes as the trivial character plus the
`m` two-dimensional characters `rotChar n 1, …, rotChar n m`.

For `n = 5` this is the classical pentagon statement `5 = 1 + 2 + 2`.
-/

open Finset

namespace Brockian

open DihedralGroup

variable {n : ℕ}

/-- For an odd `n`-gon every reflection fixes exactly one vertex. -/

theorem permChar_odd_decomposition (m : ℕ) (g : DihedralGroup (2 * m + 1)) :
    permChar (2 * m + 1) g
      = trivChar (2 * m + 1) g + ∑ j ∈ Finset.Icc 1 m, rotChar (2 * m + 1) j g := by
  have hodd : Odd (2 * m + 1) := ⟨m, by omega⟩
  cases g with
  | sr i =>
    rw [permChar_sr_odd hodd i]
    simp [trivChar, rotChar]
  | r i =>
    have hsum : ∑ j ∈ Finset.Icc 1 m, ((rotChar (2 * m + 1) j (r i) : ℝ) : ℂ)
        = ∑ j ∈ Finset.Icc 1 m,
            ((ZMod.stdAddChar i) ^ j + (ZMod.stdAddChar i) ^ (2 * m + 1 - j)) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [Finset.mem_Icc] at hj
      exact rotChar_r_eq_rootPow i j (by omega)
    have hLHS : ((permChar (2 * m + 1) (r i) : ℝ) : ℂ)
        = if i = 0 then ((2 * m + 1 : ℕ) : ℂ) else 0 := by
      by_cases h : i = 0
      · subst h; rw [permChar_r_zero, if_pos rfl]; push_cast; ring
      · rw [permChar_r_of_ne_zero h, if_neg h, Complex.ofReal_zero]
    have hgoal : ((permChar (2 * m + 1) (r i) : ℝ) : ℂ)
        = ((trivChar (2 * m + 1) (r i) : ℝ) : ℂ)
          + ∑ j ∈ Finset.Icc 1 m, ((rotChar (2 * m + 1) j (r i) : ℝ) : ℂ) := by
      calc ((permChar (2 * m + 1) (r i) : ℝ) : ℂ)
          = if i = 0 then ((2 * m + 1 : ℕ) : ℂ) else 0 := hLHS
        _ = ∑ k ∈ Finset.range (2 * m + 1), (ZMod.stdAddChar i : ℂ) ^ k :=
            (sum_pow_stdAddChar i).symm
        _ = (ZMod.stdAddChar i : ℂ) ^ 0
              + ∑ j ∈ Finset.Icc 1 m,
                  ((ZMod.stdAddChar i : ℂ) ^ j + (ZMod.stdAddChar i : ℂ) ^ (2 * m + 1 - j)) :=
            sum_range_odd_split m _
        _ = ((trivChar (2 * m + 1) (r i) : ℝ) : ℂ)
              + ∑ j ∈ Finset.Icc 1 m, ((rotChar (2 * m + 1) j (r i) : ℝ) : ℂ) := by
            rw [hsum]
            simp [trivChar]
    exact_mod_cast hgoal

/-- The pentagon: the permutation representation on the five vertices is the sum of the
trivial representation and the two two-dimensional representations, `5 = 1 + 2 + 2`. -/
