/-
# Bell Theorem
Category: Frontier Physics
Target: Frontier.bell_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bell Theorem
Category: Frontier Physics
Target: Frontier.bell_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open MeasureTheory Matrix

namespace Frontier

/-! ## The classical (local hidden variable) side -/

/-- The pointwise CHSH bound: if four numbers `a₀, a₁, b₀, b₁` have absolute value at most `1`
(the possible outcomes, or local averages of outcomes, of `±1`-valued measurements), then the
CHSH combination is bounded by `2` in absolute value. -/

theorem LHVModel.abs_chsh_le_two (M : LHVModel) :
    |M.corr 0 0 + M.corr 0 1 + M.corr 1 0 - M.corr 1 1| ≤ 2 := by
  have hsum : M.corr 0 0 + M.corr 0 1 + M.corr 1 0 - M.corr 1 1 =
      ∫ ω, (M.a 0 ω * M.b 0 ω + M.a 0 ω * M.b 1 ω + M.a 1 ω * M.b 0 ω
        - M.a 1 ω * M.b 1 ω) ∂M.μ := by
    have i01 : Integrable (fun ω => M.a 0 ω * M.b 0 ω + M.a 0 ω * M.b 1 ω) M.μ := by
      simpa using (M.hint 0 0).add (M.hint 0 1)
    have i012 : Integrable
        (fun ω => M.a 0 ω * M.b 0 ω + M.a 0 ω * M.b 1 ω + M.a 1 ω * M.b 0 ω) M.μ := by
      simpa using i01.add (M.hint 1 0)
    simp only [LHVModel.corr]
    rw [← integral_add (M.hint 0 0) (M.hint 0 1), ← integral_add i01 (M.hint 1 0),
      ← integral_sub i012 (M.hint 1 1)]
  have hInt : Integrable (fun ω => M.a 0 ω * M.b 0 ω + M.a 0 ω * M.b 1 ω + M.a 1 ω * M.b 0 ω
      - M.a 1 ω * M.b 1 ω) M.μ :=
    (((M.hint 0 0).add (M.hint 0 1)).add (M.hint 1 0)).sub (M.hint 1 1)
  rw [hsum]
  refine (abs_integral_le_integral_abs).trans ?_
  have hmono : ∫ ω, |M.a 0 ω * M.b 0 ω + M.a 0 ω * M.b 1 ω + M.a 1 ω * M.b 0 ω
      - M.a 1 ω * M.b 1 ω| ∂M.μ ≤ ∫ _ω, (2 : ℝ) ∂M.μ := by
    refine integral_mono hInt.abs (integrable_const 2) fun ω => ?_
    exact abs_chsh_pointwise_le_two (M.ha 0 ω) (M.ha 1 ω) (M.hb 0 ω) (M.hb 1 ω)
  simpa using hmono

/-! ## The quantum side: an explicit two-qubit model violating the CHSH bound -/

/-- `s = 1/√2`. -/
