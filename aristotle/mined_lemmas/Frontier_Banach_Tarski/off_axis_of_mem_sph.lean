/-
Absorbing the countable set of poles: the unit sphere is `SO(3)`-paradoxical.
-/
import RequestProject.Sphere

open Matrix Set Pointwise

namespace BT

noncomputable section

/-! ### Countability of the solution sets of rotation equations -/

/-- For a point `d` off the `z`-axis, only countably many angles `t` satisfy
`rZ (c * t) • d = d'`. -/

theorem off_axis_of_mem_sph {x : E} (hx : x ∈ sph) (h1 : x ≠ EuclideanSpace.single 2 (1 : ℝ))
    (h2 : x ≠ -EuclideanSpace.single 2 (1 : ℝ)) : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hx0, hx1⟩ := hcon
  have hnorm : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_eq_dotProduct]
    simp [dotProduct, Fin.sum_univ_three]
    ring
  have h1' : ‖x‖ = 1 := hx
  have hsq : x 2 ^ 2 = 1 := by rw [h1', hx0, hx1] at hnorm; nlinarith
  have : x 2 = 1 ∨ x 2 = -1 := by
    rcases mul_eq_zero.mp (show (x 2 - 1) * (x 2 + 1) = 0 by nlinarith) with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases this with h | h
  · exact h1 (by ext i; fin_cases i <;>
      simp [EuclideanSpace.single_apply, hx0, hx1, h])
  · exact h2 (by ext i; fin_cases i <;>
      simp [EuclideanSpace.single_apply, hx0, hx1, h])

end

end BT

/-
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.Ball

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Pointwise

namespace Frontier

/-- **The Banach–Tarski paradox.**

The closed unit ball `B` of `ℝ³` admits a paradoxical decomposition: there are two disjoint
subsets `P, Q ⊆ B`, each of which is equidecomposable with the whole ball `B` using finitely
many pieces moved by isometries of `ℝ³`.

Here `BT.Equidec G A B` says that there is a finite decomposition of `A` into pieces which,
after applying to each piece a single element of the group `G`, reassemble exactly into `B`
(this is Mathlib's `Equidecomp`), and `G` is the full isometry group
`EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3)`. -/
