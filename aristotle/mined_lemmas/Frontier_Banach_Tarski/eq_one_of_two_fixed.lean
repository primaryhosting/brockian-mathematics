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


lemma eq_one_of_two_fixed (M : SO3) {u v : Fin 3 → ℝ} (hu1 : u ⬝ᵥ u = 1) (hv1 : v ⬝ᵥ v = 1)
    (hu : M.1 *ᵥ u = u) (hv : M.1 *ᵥ v = v) (h1 : v ≠ u) (h2 : v ≠ -u) : M.1 = 1 := by
  have hc : cross3 u v ≠ 0 := by
    intro hc0
    rcases cross_eq_zero_cases hu1 hv1 hc0 with h | h
    · exact h1 h
    · exact h2 h
  have hcc : cross3 u v ⬝ᵥ cross3 u v ≠ 0 := fun h => hc (dot_self_eq_zero h)
  exact eq_one_of_fixes hu hv (cross_fixed M hu hv) hcc

/-- The unit sphere of `ℝ³`. -/
