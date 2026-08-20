/-
  Aristotle target — the Weyl b→∞ limit-point/limit-circle DICHOTOMY (radius side).

  This is the missing link between the verified finite-b nested-circle geometry
  (`Brockian.Weyl.Disk`: radius r_b = 1/(2|Im λ|·∫₀ᵇ|φ|²), monotone) and the
  essential-self-adjointness criterion (`Brockian.Weyl.Cayley`).

  The mathematical core is a self-contained real-analysis fact: for a positive
  constant c and a nonnegative nondecreasing accumulation I(b) (= ∫₀ᵇ|φ|²),
      r(b) = 1/(2·c·I(b))  →  0   as b → ∞   ⟺   I(b) → ∞.
  (limit-point side: radius shrinks to a point iff the L² mass diverges.)

  The originally requested equivalence omitted the necessary condition that the
  mass is positive somewhere. In Lean's field convention, `1 / 0 = 0`, so the
  identically-zero mass is a counterexample: its radius is identically zero but
  its mass does not tend to `+∞`. The counterexample is proved below, followed by
  the corrected nondegenerate equivalence and the two valid requested results.
-/
import Mathlib

open Filter Topology

namespace Brockian.Weyl.DichotomyTarget

/-- The hypotheses in the originally proposed `radius_tendsto_zero_iff` do not
suffice: the identically-zero mass is a counterexample because Lean defines
`1 / 0 = 0`. -/

theorem radius_tendsto_zero_iff_of_pos (c : ℝ) (hc : 0 < c)
    (I : ℝ → ℝ) (hI0 : ∀ b, 0 ≤ I b) (hImono : Monotone I)
    (hIpos : ∃ b, 0 < I b) :
    Tendsto (fun b => 1 / (2 * c * I b)) atTop (𝓝 0) ↔ Tendsto I atTop atTop := by
  constructor
  · intro hr
    obtain ⟨b₀, hb₀⟩ := hIpos
    have hc2 : 0 < 2 * c := by positivity
    have hevent : ∀ᶠ b in atTop, 2 * c * I b > 0 := by
      filter_upwards [eventually_ge_atTop b₀] with b hb
      exact mul_pos hc2 (lt_of_lt_of_le hb₀ (hImono hb))
    have hinv : Tendsto (fun b => (2 * c * I b)⁻¹) atTop
        (nhdsWithin 0 (Set.Ioi 0)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · simpa only [one_div] using hr
      · filter_upwards [hevent] with b hb
        exact inv_pos.mpr hb
    have hx := hinv.inv_tendsto_nhdsGT_zero
    have hprod : Tendsto (fun b => 2 * c * I b) atTop atTop := by
      convert hx using 1
      ext b
      simp
    exact (tendsto_const_mul_atTop_of_pos hc2).mp hprod
  · intro hdiv
    have hc2 : 0 < 2 * c := by positivity
    have hprod : Tendsto (fun b => 2 * c * I b) atTop atTop :=
      Tendsto.const_mul_atTop hc2 hdiv
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hprod

/-- The limit-point case: if the L² mass diverges, the radius collapses to a point. -/
