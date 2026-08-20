import Mathlib
open Matrix
namespace C2.Phys3

theorem spin_sq_id : Sx*Sx = 1 ∧ Sy*Sy = 1 ∧ Sz*Sz = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Sx, Sy, Sz, ← Matrix.ext_iff, Matrix.one_apply, Complex.I_mul_I]

