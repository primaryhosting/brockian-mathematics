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

lemma indicator_diag {n : ℕ} {A : Finset (Fin n → ZMod 3)}
    (hA : ThreeAPFree (A : Set (Fin n → ZMod 3))) (x y z : A) :
    (if x = y ∧ y = z then (1 : ZMod 3) else 0)
      = if (x : Fin n → ZMod 3) + (y : Fin n → ZMod 3) + (z : Fin n → ZMod 3) = 0
        then (1 : ZMod 3) else 0 := by
  by_cases h : (x : Fin n → ZMod 3) + (y : Fin n → ZMod 3) + (z : Fin n → ZMod 3) = 0
  · obtain ⟨h1, h2⟩ := eq_of_sum_eq_zero hA x.2 y.2 z.2 h
    rw [if_pos h, if_pos ⟨Subtype.ext h1, Subtype.ext h2⟩]
  · rw [if_neg h, if_neg]
    rintro ⟨rfl, rfl⟩
    apply h
    funext i
    have : (3 : ZMod 3) * (x : Fin n → ZMod 3) i = 0 := by
      rw [show (3:ZMod 3) = 0 from by decide]; ring
    simp only [Pi.add_apply, Pi.zero_apply]
    linear_combination this

/-- **The Ellenberg–Gijswijt bound.** -/
