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

theorem countable_rY_sol {d v : E} (hv : v 0 ≠ 0 ∨ v 2 ≠ 0) :
    {s : ℝ | rY s • v = d}.Countable := by
  rcases Set.eq_empty_or_nonempty {s : ℝ | rY s • v = d} with h | ⟨s₀, hs₀⟩
  · rw [h]; exact Set.countable_empty
  · refine Set.Countable.mono ?_
      (Set.countable_range (fun k : ℤ => s₀ + (k : ℝ) * (2 * Real.pi)))
    intro s hs
    have heq : rY s • v = rY s₀ • v := by
      rw [show rY s • v = d from hs, show rY s₀ • v = d from hs₀]
    have hfix : rY (s - s₀) • v = v := by
      have hsplit : rY (s - s₀) = (rY s₀)⁻¹ * rY s := by
        rw [rY_inv, ← rY_add]; congr 1; ring
      rw [hsplit, SemigroupAction.mul_smul, heq, inv_smul_smul]
    obtain ⟨hcos, -⟩ := rY_fix _ v hv hfix
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp hcos
    exact ⟨k, by show s₀ + (k : ℝ) * (2 * Real.pi) = s; linarith⟩

/-- The reals are uncountable, so a countable set of reals has a complement point. -/
