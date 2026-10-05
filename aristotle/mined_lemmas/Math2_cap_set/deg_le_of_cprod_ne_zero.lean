import RequestProject.CapExpand

/-!
# The Ellenberg–Gijswijt bound

Combining the slice-rank bound with the polynomial expansion gives
`|A| ≤ 3 · #{exponent vectors of degree ≤ 2n/3}` for every 3AP-free `A ⊆ 𝔽₃ⁿ`.
-/

open scoped BigOperators
open Finset

namespace CapSetAux

/-- In `𝔽₃ⁿ`, a 3AP-free set contains no nontrivial triple summing to zero. -/

lemma deg_le_of_cprod_ne_zero (g : Idx n) (hg : cprod n g ≠ 0) :
    deg n (e₁ n g) + deg n (e₂ n g) + deg n (e₃ n g) ≤ 2 * n := by
  have hall : ∀ i : Fin n, cf (g i) ≠ 0 := by
    intro i hi
    exact hg (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  have : deg n (e₁ n g) + deg n (e₂ n g) + deg n (e₃ n g)
      = ∑ i : Fin n, (((g i).1 : ℕ) + ((g i).2.1 : ℕ) + ((g i).2.2 : ℕ)) := by
    simp [deg, e₁, e₂, e₃, Finset.sum_add_distrib]
  rw [this]
  calc ∑ i : Fin n, (((g i).1 : ℕ) + ((g i).2.1 : ℕ) + ((g i).2.2 : ℕ))
      ≤ ∑ _i : Fin n, 2 := Finset.sum_le_sum fun i _ => cf_deg (g i) (hall i)
    _ = 2 * n := by simp [mul_comm]

variable (n)

/-- The three groups of terms. -/
