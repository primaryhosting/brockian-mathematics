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

theorem radius_tendsto_zero_iff_counterexample :
    ∃ (c : ℝ) (I : ℝ → ℝ),
      0 < c ∧ (∀ b, 0 ≤ I b) ∧ Monotone I ∧
      Tendsto (fun b => 1 / (2 * c * I b)) atTop (𝓝 0) ∧
      ¬ Tendsto I atTop atTop := by
  use 1, fun _ => 0
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩
  · exact fun _ => le_refl 0
  · exact monotone_const
  · simp
  · intro h
    exact not_tendsto_atTop_of_tendsto_nhds (tendsto_const_nhds (x := (0 : ℝ))) h

/-
The requested theorem cannot be retained as a declaration, since the preceding
counterexample proves it false. Its exact original statement was:

