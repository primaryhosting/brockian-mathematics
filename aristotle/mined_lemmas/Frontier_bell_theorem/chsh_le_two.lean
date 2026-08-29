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

open MeasureTheory

namespace Frontier

/-- Pointwise CHSH inequality: for outcomes in `[-1, 1]`, the CHSH combination is
bounded by `2`. -/

theorem chsh_le_two {Ω : Type} [MeasurableSpace Ω] (M : LHVModel Ω) :
    |M.chsh| ≤ 2 := by
  haveI := M.isProb
  have h00 := M.intAB 0 0
  have h01 := M.intAB 0 1
  have h10 := M.intAB 1 0
  have h11 := M.intAB 1 1
  simp only [LHVModel.chsh, LHVModel.corr] at *
  norm_num at h00 h01 h10 h11 ⊢
  have hsum2 : Integrable (fun ω => M.A₁ ω * M.B₁ ω + M.A₁ ω * M.B₂ ω) M.μ := h00.add h01
  have hsum3 : Integrable
      (fun ω => M.A₁ ω * M.B₁ ω + M.A₁ ω * M.B₂ ω + M.A₂ ω * M.B₁ ω) M.μ := hsum2.add h10
  have hsum4 : Integrable
      (fun ω => M.A₁ ω * M.B₁ ω + M.A₁ ω * M.B₂ ω + M.A₂ ω * M.B₁ ω - M.A₂ ω * M.B₂ ω) M.μ :=
    hsum3.sub h11
  have hsplit : ∫ ω, (M.A₁ ω * M.B₁ ω + M.A₁ ω * M.B₂ ω + M.A₂ ω * M.B₁ ω
      - M.A₂ ω * M.B₂ ω) ∂M.μ
      = (∫ ω, M.A₁ ω * M.B₁ ω ∂M.μ) + (∫ ω, M.A₁ ω * M.B₂ ω ∂M.μ)
        + (∫ ω, M.A₂ ω * M.B₁ ω ∂M.μ) - (∫ ω, M.A₂ ω * M.B₂ ω ∂M.μ) := by
    rw [integral_sub hsum3 h11, integral_add hsum2 h10, integral_add h00 h01]
  rw [← hsplit]
  refine (abs_integral_le_integral_abs).trans ?_
  have hbound : ∀ ω, |M.A₁ ω * M.B₁ ω + M.A₁ ω * M.B₂ ω + M.A₂ ω * M.B₁ ω
      - M.A₂ ω * M.B₂ ω| ≤ 2 := fun ω =>
    chsh_pointwise _ _ _ _ (M.hA₁ ω) (M.hA₂ ω) (M.hB₁ ω) (M.hB₂ ω)
  calc ∫ ω, |M.A₁ ω * M.B₁ ω + M.A₁ ω * M.B₂ ω + M.A₂ ω * M.B₁ ω - M.A₂ ω * M.B₂ ω| ∂M.μ
      ≤ ∫ _ω, (2 : ℝ) ∂M.μ := by
        exact integral_mono hsum4.abs (integrable_const 2) hbound
    _ = 2 := by simp

/-- A local hidden-variable model on a one-point hidden-variable space, all outcomes `+1`.
It witnesses that the notion of a local hidden-variable model is not vacuous, and that the
classical CHSH bound `2` is attained. -/
