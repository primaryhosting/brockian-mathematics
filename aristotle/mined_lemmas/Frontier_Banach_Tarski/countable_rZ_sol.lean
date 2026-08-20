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

theorem countable_rZ_sol {c : ℝ} (hc : c ≠ 0) {d d' : E} (hd : d 0 ≠ 0 ∨ d 1 ≠ 0) :
    {t : ℝ | rZ (c * t) • d = d'}.Countable := by
  rcases Set.eq_empty_or_nonempty {t : ℝ | rZ (c * t) • d = d'} with h | ⟨t₀, ht₀⟩
  · rw [h]; exact Set.countable_empty
  · refine Set.Countable.mono ?_
      (Set.countable_range (fun k : ℤ => t₀ + (k : ℝ) * (2 * Real.pi) / c))
    intro t ht
    have heq : rZ (c * t) • d = rZ (c * t₀) • d := by
      rw [show rZ (c * t) • d = d' from ht, show rZ (c * t₀) • d = d' from ht₀]
    have hfix : rZ (c * (t - t₀)) • d = d := by
      have hsplit : rZ (c * (t - t₀)) = (rZ (c * t₀))⁻¹ * rZ (c * t) := by
        rw [rZ_inv, ← rZ_add]; congr 1; ring
      rw [hsplit, SemigroupAction.mul_smul, heq, inv_smul_smul]
    obtain ⟨hcos, -⟩ := rZ_fix _ d hd hfix
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp hcos
    refine ⟨k, ?_⟩
    show t₀ + (k : ℝ) * (2 * Real.pi) / c = t
    field_simp
    linear_combination hk

/-- For a point `v` off the `y`-axis, only countably many angles `s` satisfy
`rY s • v = d`. -/
