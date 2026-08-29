import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Metric Set

namespace Brouwer2D

noncomputable section

/-- The punctured complex plane, the base of the exponential covering map. -/
abbrev Cstar := {z : ℂ // z ≠ 0}

/-- The exponential covering map `ℂ → ℂ \ {0}`. -/

theorem continuous_ww (hf : ContinuousOn f (closedBall (0 : ℂ) 1)) :
    Continuous fun p : ℝ × ℝ => ww f p.1 p.2 := by
  have hz : Continuous fun p : ℝ × ℝ => (aa p.1 : ℂ) * ee p.2 := by
    have h1 : Continuous fun p : ℝ × ℝ => ((aa p.1 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_aa.comp continuous_fst)
    exact h1.mul (continuous_ee.comp continuous_snd)
  have hfc : Continuous fun p : ℝ × ℝ => f ((aa p.1 : ℂ) * ee p.2) :=
    hf.comp_continuous hz fun p => arg_mem_ball p.1 p.2
  have hb : Continuous fun p : ℝ × ℝ => ((bb p.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_bb.comp continuous_fst)
  exact hz.sub (hb.mul hfc)

