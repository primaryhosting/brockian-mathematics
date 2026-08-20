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


lemma eq_one_of_fixes {M : Matrix (Fin 3) (Fin 3) ℝ} {u v : Fin 3 → ℝ}
    (hu : M *ᵥ u = u) (hv : M *ᵥ v = v) (hc : M *ᵥ cross3 u v = cross3 u v)
    (hne : cross3 u v ⬝ᵥ cross3 u v ≠ 0) : M = 1 := by
  set c := cross3 u v with hcdef
  set P : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j => (![u, v, c] j) i with hP
  have hdet : P.det = c ⬝ᵥ c := by
    simp [hP, Matrix.det_fin_three, hcdef, cross3, dotProduct, Fin.sum_univ_three]; ring
  have hNP : (M - 1) * P = 0 := by
    ext i j
    have hcol : ((M - 1) * P) i j = ((M - 1) *ᵥ (![u, v, c] j)) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hP]
    rw [hcol]
    fin_cases j <;> simp [Matrix.sub_mulVec, hu, hv, hc]
  have hPunit : IsUnit P.det := by rw [hdet]; exact isUnit_iff_ne_zero.mpr hne
  have h2 := congrArg (fun X => X * P⁻¹) hNP
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv P hPunit, Matrix.mul_one,
    Matrix.zero_mul] at h2
  exact sub_eq_zero.mp h2

/-- A rotation fixes the cross product of two of its fixed vectors. -/
