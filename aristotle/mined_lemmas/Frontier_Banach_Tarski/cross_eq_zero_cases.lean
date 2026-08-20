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


lemma cross_eq_zero_cases {u v : Fin 3 → ℝ} (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1)
    (h : cross3 u v = 0) : v = u ∨ v = -u := by
  have hlag : cross3 u v ⬝ᵥ cross3 u v = (u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ 2 := by
    simp [cross3, dotProduct, Fin.sum_univ_three]; ring
  rw [h, hu, hv] at hlag
  simp at hlag
  have ht : (u ⬝ᵥ v) ^ 2 = 1 := by linarith [hlag]
  set t := u ⬝ᵥ v with htdef
  have hw : (v - t • u) ⬝ᵥ (v - t • u) = 0 := by
    have h1 : (v - t • u) ⬝ᵥ (v - t • u) = v ⬝ᵥ v - 2 * t * (u ⬝ᵥ v) + t ^ 2 * (u ⬝ᵥ u) := by
      simp [dotProduct, Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply]; ring
    rw [h1, hu, hv, ← htdef]
    nlinarith [ht]
  have hvt : v = t • u := sub_eq_zero.mp (dot_self_eq_zero hw)
  have hfac : (t - 1) * (t + 1) = 0 := by nlinarith [ht]
  rcases mul_eq_zero.mp hfac with h1 | h1
  · left; rw [hvt, show t = 1 by linarith, one_smul]
  · right; rw [hvt, show t = -1 by linarith]; simp

