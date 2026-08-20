import Mathlib
open intervalIntegral MeasureTheory
namespace C2.An4

/-- Fundamental theorem of calculus: if `F` has derivative `f` everywhere and `f` is
continuous, then `∫ x in a..b, f x = F b - F a`. -/

theorem uniform_cont_on_compact (f : ℝ → ℝ) (a b : ℝ) (hf : ContinuousOn f (Set.Icc a b)) :
    UniformContinuousOn f (Set.Icc a b) :=
  isCompact_Icc.uniformContinuousOn_of_continuous hf

end C2.An4

