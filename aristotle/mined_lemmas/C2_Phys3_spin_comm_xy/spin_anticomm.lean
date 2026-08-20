import Mathlib
open Matrix
namespace C2.Phys3

theorem spin_anticomm : Sx*Sy + Sy*Sx = 0 := by
  simp [Sx, Sy, ← Matrix.ext_iff]

end C2.Phys3

