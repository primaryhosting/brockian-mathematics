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

theorem fixed_countable (M : SO3) (hM : M ≠ 1) : {x ∈ sph | M • x = x}.Countable := by
  rcases Set.eq_empty_or_nonempty {x ∈ sph | M • x = x} with h | ⟨u, hu⟩
  · rw [h]; exact Set.countable_empty
  · have hsub : {x ∈ sph | M • x = x} ⊆ {u, -u} := by
      intro v hv
      by_contra hne
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
      apply hM
      have hgram := gram_ne_zero (u := u) (v := v) hu.1 hv.1
        (fun h => hne.1 h.symm) (fun h => hne.2 (by rw [h]; module))
      have hNu : (M : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ u.ofLp = u.ofLp := by
        rw [← smul_ofLp, hu.2]
      have hNv : (M : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v.ofLp = v.ofLp := by
        rw [← smul_ofLp, hv.2]
      exact Subtype.ext (so3_eq_one_of_fixed_pair (so3_transpose_mul M) (so3_det M) hgram hNu hNv)
    exact Set.Countable.mono hsub (Set.toFinite _).countable

instance : Countable F2 := FreeGroup.toWord_injective.countable

/-- The countable set of points of the sphere fixed by some nontrivial rotation of our free
group. -/
