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

theorem exists_angle {D : Set E} (hD : D ⊆ sph) (hcount : D.Countable)
    (hp : EuclideanSpace.single 2 (1 : ℝ) ∉ D) (hp' : -EuclideanSpace.single 2 (1 : ℝ) ∉ D) :
    ∃ t : ℝ, ∀ n : ℕ, 1 ≤ n → Disjoint ((rZ t ^ n) • D) D := by
  have hoff : ∀ d ∈ D, d 0 ≠ 0 ∨ d 1 ≠ 0 := fun d hd =>
    off_axis_of_mem_sph (hD hd) (fun h => hp (h ▸ hd)) (fun h => hp' (h ▸ hd))
  obtain ⟨t, ht⟩ := exists_not_mem_of_countable
    (S := ⋃ (n : ℕ), ⋃ (d ∈ D), ⋃ (d' ∈ D), {t : ℝ | rZ (((n : ℝ) + 1) * t) • d = d'})
    (Set.countable_iUnion fun n =>
      hcount.biUnion fun d hd => hcount.biUnion fun d' _ =>
        countable_rZ_sol (by positivity) (hoff d hd))
  refine ⟨t, fun n hn => ?_⟩
  rw [Set.disjoint_left]
  rintro _ ⟨d, hd, rfl⟩ hmem
  apply ht
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine Set.mem_iUnion.2 ⟨m, Set.mem_iUnion₂.2 ⟨d, hd, Set.mem_iUnion₂.2
    ⟨(rZ t ^ (m + 1)) • d, hmem, ?_⟩⟩⟩
  show rZ (((m : ℝ) + 1) * t) • d = (rZ t ^ (m + 1)) • d
  rw [rZ_pow]
  norm_num

/-- There is a rotation taking the poles off a given countable subset of the sphere. -/
