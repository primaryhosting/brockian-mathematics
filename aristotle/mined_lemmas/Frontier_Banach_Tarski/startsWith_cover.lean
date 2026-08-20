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

theorem startsWith_cover (i : Fin 2) :
    startsWith (i, true) ∪ (FreeGroup.of i : F2) • startsWith (i, false) = Set.univ := by
  ext w
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases h : w.toWord.head? = some (i, true)
  · exact Or.inl h
  · refine Or.inr ⟨(FreeGroup.of i : F2)⁻¹ * w, ?_, by simp⟩
    show ((FreeGroup.of i : F2)⁻¹ * w).toWord.head? = some (i, false)
    rw [inv_of_eq_mk]
    rw [FreeWord.toWord_cons (x := (i, false)) (by simpa using h)]
    simp

