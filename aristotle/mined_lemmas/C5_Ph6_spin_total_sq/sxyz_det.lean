import Mathlib
open Matrix
namespace C5.Ph6

theorem sxyz_det : Sx.det = -1 := by
  simp [Sx, Matrix.det_fin_two_of]
end C5.Ph6

