import Mathlib
namespace Brockian.MsViviani
/-- Ptolemy's inequality: for any four points in an inner product space,
    dist A C · dist B D ≤ dist A B · dist C D + dist B C · dist A D. -/
theorem ptolemy_inequality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A B C D : E) :
    dist A C * dist B D ≤ dist A B * dist C D + dist B C * dist A D := by
  sorry
end Brockian.MsViviani
