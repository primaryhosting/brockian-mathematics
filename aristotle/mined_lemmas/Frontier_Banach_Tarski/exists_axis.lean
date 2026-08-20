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

theorem exists_axis {D : Set E} (hcount : D.Countable) :
    ∃ Q : SO3, EuclideanSpace.single 2 (1 : ℝ) ∉ Q⁻¹ • D ∧
      -EuclideanSpace.single 2 (1 : ℝ) ∉ Q⁻¹ • D := by
  set p : E := EuclideanSpace.single 2 (1 : ℝ) with hpdef
  have hoffp : p 0 ≠ 0 ∨ p 2 ≠ 0 := Or.inr (by simp [hpdef, EuclideanSpace.single_apply])
  have hoffnp : (-p) 0 ≠ 0 ∨ (-p) 2 ≠ 0 := Or.inr (by simp [hpdef, EuclideanSpace.single_apply])
  obtain ⟨psi, hpsi⟩ := exists_not_mem_of_countable
    (S := ⋃ (d ∈ D), ({s : ℝ | rY s • p = d} ∪ {s : ℝ | rY s • (-p) = d}))
    (hcount.biUnion fun _ _ => (countable_rY_sol hoffp).union (countable_rY_sol hoffnp))
  refine ⟨rY psi, ?_, ?_⟩
  · rintro ⟨d, hd, hdq⟩
    replace hdq : (rY psi)⁻¹ • d = p := hdq
    exact hpsi (Set.mem_iUnion₂.2 ⟨d, hd, Or.inl (by
      show rY psi • p = d
      rw [← hdq, smul_inv_smul])⟩)
  · rintro ⟨d, hd, hdq⟩
    replace hdq : (rY psi)⁻¹ • d = -p := hdq
    exact hpsi (Set.mem_iUnion₂.2 ⟨d, hd, Or.inr (by
      show rY psi • (-p) = d
      rw [← hdq, smul_inv_smul])⟩)

