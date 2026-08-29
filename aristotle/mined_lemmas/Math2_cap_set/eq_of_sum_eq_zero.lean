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

lemma eq_of_sum_eq_zero {n : ℕ} {A : Finset (Fin n → ZMod 3)}
    (hA : ThreeAPFree (A : Set (Fin n → ZMod 3)))
    {x y z : Fin n → ZMod 3} (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
    (h : x + y + z = 0) : x = y ∧ y = z := by
  have hxy : x = y := by
    refine hA (by exact_mod_cast hx) (by exact_mod_cast hy) (by exact_mod_cast hz) ?_
    funext i
    have hi : x i + y i + z i = 0 := by simpa using congrFun h i
    have : (3 : ZMod 3) = 0 := by decide
    have hy3 : y i + y i = -y i := by
      have : y i + y i + y i = 0 := by
        have : (3 : ZMod 3) * y i = 0 := by rw [show (3:ZMod 3) = 0 from by decide]; ring
        linear_combination this
      linear_combination this
    simp only [Pi.add_apply]
    rw [hy3]
    linear_combination hi
  subst hxy
  refine ⟨rfl, ?_⟩
  funext i
  have hi : x i + x i + z i = 0 := by simpa using congrFun h i
  have h3 : x i + x i + x i = 0 := by
    have : (3 : ZMod 3) * x i = 0 := by rw [show (3:ZMod 3) = 0 from by decide]; ring
    linear_combination this
  linear_combination h3 - hi

/-- The zero-sum indicator is the diagonal indicator on a 3AP-free set. -/
