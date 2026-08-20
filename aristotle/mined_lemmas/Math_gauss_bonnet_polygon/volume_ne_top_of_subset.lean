import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma volume_ne_top_of_subset {S : Set E3} (h : S ⊆ unitBall3) : volume S ≠ ⊤ :=
  ne_top_of_le_ne_top volume_unitBall3_ne_top (measure_mono h)

/-- The antipodal map exchanges opposite octants. -/
