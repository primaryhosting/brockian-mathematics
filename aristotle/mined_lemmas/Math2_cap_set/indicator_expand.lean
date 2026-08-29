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

lemma indicator_expand (x y z : Fin n → ZMod 3) :
    (if x + y + z = 0 then (1 : ZMod 3) else 0)
      = ∑ g : Idx n, cprod n g * mon n (e₁ n g) x * mon n (e₂ n g) y * mon n (e₃ n g) z := by
  rw [indicator_prod]
  have step : ∀ i : Fin n, (if x i + y i + z i = 0 then (1 : ZMod 3) else 0)
      = ∑ t : Fin 3 × Fin 3 × Fin 3,
        cf t * x i ^ (t.1 : ℕ) * y i ^ (t.2.1 : ℕ) * z i ^ (t.2.2 : ℕ) :=
    fun i => cf_expand _ _ _
  rw [Finset.prod_congr rfl fun i _ => step i, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [cprod, mon, e₁, e₂, e₃]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

/-- Terms with a nonzero coefficient have total degree at most `2n`. -/
