import Mathlib

/-!
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

/-- The affine cuspidal cubic `{(x, y) | y ^ 2 = x ^ 3}` over a field `k`. -/

theorem hironaka_resolution_proper_real : IsProperMap (cuspRes ℝ) := by
  have hcont : Continuous (cuspRes ℝ) := by
    unfold cuspRes; fun_prop
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨hcont, fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  refine IsCompact.of_isClosed_subset (isCompact_Icc (a := -(|R| + 1)) (b := |R| + 1))
    (hK.isClosed.preimage hcont) ?_
  intro t ht
  have h1 : |t ^ 2| ≤ |R| :=
    calc |t ^ 2| = ‖(cuspRes ℝ t).1‖ := rfl
      _ ≤ ‖cuspRes ℝ t‖ := norm_fst_le _
      _ ≤ R := hR _ ht
      _ ≤ |R| := le_abs_self R
  have h3 : t ^ 2 ≤ |R| := le_trans (le_abs_self _) h1
  constructor <;> nlinarith [abs_nonneg R, sq_nonneg (t - 1), sq_nonneg (t + 1)]

/-- Over the reals the resolution map is a closed embedding of the smooth affine line onto
the cuspidal cubic: the image is exactly the curve. -/
