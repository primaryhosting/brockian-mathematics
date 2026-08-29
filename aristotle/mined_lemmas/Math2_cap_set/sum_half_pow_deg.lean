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

lemma sum_half_pow_deg (n : ℕ) :
    ∑ a : Exp n, ((1 : ℝ) / 2) ^ (deg n a) = (7 / 4) ^ n := by
  have hpow : ∀ a : Exp n, ((1 : ℝ) / 2) ^ (deg n a) = ∏ i, ((1 : ℝ) / 2) ^ ((a i : ℕ)) := by
    intro a
    rw [deg, Finset.prod_pow_eq_pow_sum]
  rw [Finset.sum_congr rfl fun a _ => hpow a,
    ← Fintype.prod_sum (fun (_ : Fin n) (k : Fin 3) => ((1 : ℝ) / 2) ^ (k : ℕ))]
  have : ∀ _i : Fin n, ∑ k : Fin 3, ((1 : ℝ) / 2) ^ (k : ℕ) = 7 / 4 := by
    intro _i
    simp [Fin.sum_univ_three]
    norm_num
  rw [Finset.prod_congr rfl fun i _ => this i]
  simp [div_pow]

/-- The basic Chernoff bound on the number of low-degree exponent vectors. -/
