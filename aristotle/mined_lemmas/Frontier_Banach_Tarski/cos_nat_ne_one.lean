import RequestProject.Paradoxical

/-!
# Banach Tarski: a free group of rotations of `ℝ³`
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

open Set Function

/-! ## A free group of rotations of `ℝ³`

Following the classical argument, the two rotations by `arccos (3/5)` about the `z`- and the
`x`-axis generate a free subgroup of `SO(3)`.  Freeness is proved by a `5`-adic argument:
a nonempty reduced word of length `n`, applied to the integral vector `(1,0,2)` and rescaled
by `5 ^ n`, gives an integral vector which is nonzero modulo `5`.
-/

namespace FreeRotations

open Matrix

/-- The special orthogonal group of `ℝ³`. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩


lemma cos_nat_ne_one {n : ℕ} (hn : 1 ≤ n) : Real.cos (n : ℝ) ≠ 1 := by
  intro h
  rw [Real.cos_eq_one_iff] at h
  obtain ⟨k, hk⟩ := h
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hk0 : (k : ℝ) ≠ 0 := by
    intro h0
    rw [h0] at hk
    simp at hk
    exact hn0 hk.symm
  have hpi : Real.pi = (n : ℝ) / (2 * (k : ℝ)) := by
    field_simp
    linarith [hk]
  have hirr : Irrational ((n : ℝ) / (2 * (k : ℝ))) := hpi ▸ irrational_pi
  refine (Rat.not_irrational ((n : ℚ) / (2 * (k : ℚ)))) ?_
  have hcast : (((n : ℚ) / (2 * (k : ℚ)) : ℚ) : ℝ) = (n : ℝ) / (2 * (k : ℝ)) := by
    push_cast
    ring
  rw [hcast]
  exact hirr

