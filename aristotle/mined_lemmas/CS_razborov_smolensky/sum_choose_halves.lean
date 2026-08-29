import RequestProject.Circuits
import RequestProject.LowDegree

/-!
# MOD_p is not approximable by low degree functions over a field of characteristic q

This is the second half of Smolensky's argument: if the function `x ↦ ζ^{|x|}`
(`ζ` a primitive `p`-th root of unity in a field `F` of characteristic `q`) agrees
with a function of degree `D` on a set `G` of inputs, then `G` is small.
-/

namespace CS

open Finset

open scoped Classical

variable {F : Type*} [Field F] {n : ℕ}

/-- The monomial `∏_{i ∈ S} ζ^{x_i}` in the transformed variables. -/

theorem sum_choose_halves (m : ℕ) :
    2 * ∑ i ∈ Finset.range m, (2 * m).choose i + (2 * m).choose m = 2 ^ (2 * m) := by
  have h1 : ∑ i ∈ Finset.range (2 * m + 1), (2 * m).choose i = 2 ^ (2 * m) :=
    Nat.sum_range_choose (2 * m)
  have hsplit : ∑ i ∈ Finset.range (m + 1), (2 * m).choose i
      + ∑ i ∈ Finset.Ico (m + 1) (2 * m + 1), (2 * m).choose i
      = ∑ i ∈ Finset.range (2 * m + 1), (2 * m).choose i :=
    Finset.sum_range_add_sum_Ico _ (by omega)
  have hIco : ∑ i ∈ Finset.Ico (m + 1) (2 * m + 1), (2 * m).choose i
      = ∑ i ∈ Finset.range m, (2 * m).choose i := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hm : 2 * m + 1 - (m + 1) = m := by omega
    rw [hm]
    rw [← Finset.sum_range_reflect (fun i => (2 * m).choose (m + 1 + i)) m]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have he : m + 1 + (m - 1 - i) = 2 * m - i := by omega
    rw [he, Nat.choose_symm (by omega)]
  rw [hIco, Finset.sum_range_succ] at hsplit
  omega

/-- The number of subsets of `Fin (2m)` of size at most `m + D`. -/
