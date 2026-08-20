import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma volume_Oct3_neg (s t u : ℝ) :
    volume (Oct3 nA nB nC (-s) (-t) (-u)) = volume (Oct3 nA nB nC s t u) := by
  rw [← volume_neg (Oct3 nA nB nC s t u)]
  congr 1
  ext x
  simp only [Oct3, Oct2, Oct1, unitBall3, mem_preimage, mem_inter_iff, mem_setOf_eq,
    inner_neg_left, norm_neg]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨⟨⟨h1, ?_⟩, ?_⟩, ?_⟩ <;> nlinarith [h2, h3, h4]
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨⟨⟨h1, ?_⟩, ?_⟩, ?_⟩ <;> nlinarith [h2, h3, h4]

variable {nA nB nC}

/-- Splitting a subset of the ball by the plane normal to `n`, in signed form. -/
