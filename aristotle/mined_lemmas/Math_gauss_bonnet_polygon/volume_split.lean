import RequestProject.Sector

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace

namespace Math

/-- Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The volume of the standard solid wedge of dihedral angle `psi` inside the unit ball:
the axis of the wedge is the first coordinate axis, and the wedge is described in the plane
of the last two coordinates as the cone spanned by `(1,0)` and `(cos psi, sin psi)`. -/

theorem volume_split (A : Set E3) (hA : MeasurableSet A) (k : E3 →ₗ[ℝ] ℝ) (hk : k ≠ 0) :
    volume A = volume (A ∩ {x | 0 ≤ k x}) + volume (A ∩ {x | 0 ≤ (-k) x}) := by
  have hnull : volume ((A ∩ {x : E3 | 0 ≤ k x}) ∩ (A ∩ {x : E3 | 0 ≤ (-k) x})) = 0 := by
    refine measure_mono_null (fun x hx => ?_)
      (Measure.addHaar_submodule volume (LinearMap.ker k) ?_)
    · simp only [mem_inter_iff, mem_setOf_eq, LinearMap.neg_apply] at hx
      exact SetLike.mem_coe.2 (LinearMap.mem_ker.2 (le_antisymm (by linarith [hx.2.2]) hx.1.2))
    · intro hker
      exact hk (by ext x; exact LinearMap.mem_ker.1 (hker ▸ Submodule.mem_top))
  have hsplit := measure_union_add_inter (μ := volume) (A ∩ {x : E3 | 0 ≤ k x})
    (hA.inter (measurableSet_halfspace (-k)))
  rw [hnull, add_zero] at hsplit
  rw [← hsplit]
  congr 1
  ext x
  simp only [mem_union, mem_inter_iff, mem_setOf_eq, LinearMap.neg_apply]
  constructor
  · intro hx
    rcases le_total 0 (k x) with hx' | hx'
    · exact Or.inl ⟨hx, hx'⟩
    · exact Or.inr ⟨hx, by linarith⟩
  · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx

