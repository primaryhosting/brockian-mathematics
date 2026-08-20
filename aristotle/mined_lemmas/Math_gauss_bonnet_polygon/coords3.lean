import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

noncomputable def coords3 : (ℝ × ℝ) × ℝ → (Fin 3 → ℝ) := fun q => ![q.1.1, q.1.2, q.2]

