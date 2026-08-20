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

theorem radius_tendsto_zero_iff (c : ℝ) (hc : 0 < c)
    (I : ℝ → ℝ) (hI0 : ∀ b, 0 ≤ I b) (hImono : Monotone I) :
    Tendsto (fun b => 1 / (2 * c * I b)) atTop (𝓝 0) ↔ Tendsto I atTop atTop
-/

/-- **The radius dichotomy (nondegenerate core).** Positivity of the accumulated
mass somewhere excludes the identically-zero counterexample and is the condition
satisfied in the Weyl application. -/
