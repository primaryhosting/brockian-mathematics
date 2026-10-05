import Mathlib

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

import Mathlib

/-!
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Math2

/-! ## The singular plane curves `y ^ n = x ^ (n + 1)` and their normalization -/

/-- The plane affine curve `C_n : y ^ n = x ^ (n + 1)` over a field `k`.
For `n ≥ 2` this curve has a single singular point, at the origin
(for `n = 2` it is the classical cuspidal cubic `y ^ 2 = x ^ 3`). -/

lemma isPlaneCurveResolution_cusp {k : Type*} [Field k] {n : ℕ} (hn : 1 ≤ n) :
    IsPlaneCurveResolution (cuspCurve k n) {((0, 0) : k × k)} (cuspParam k n)
      (cuspParamInv k) {t : k | t ≠ 0} where
  singular_subset := by
    rintro p rfl
    exact zero_mem_cuspCurve hn
  mapsTo := cuspParam_mem n
  injective := cuspParam_injective n hn
  surjective := by
    intro p hp
    rcases eq_or_ne p (0, 0) with rfl | hp0
    · exact ⟨0, (cuspParam_eq_zero_iff hn 0).2 rfl⟩
    · exact ⟨cuspParamInv k p, cuspParam_cuspParamInv n hp (cuspCurve_fst_ne_zero hn hp hp0)⟩
  preimage_smooth := by
    intro t
    simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact not_congr (cuspParam_eq_zero_iff hn t)
  left_inv := fun t ht => cuspParamInv_cuspParam n ht
  right_inv := by
    intro p hp
    exact cuspParam_cuspParamInv n hp.1
      (cuspCurve_fst_ne_zero hn hp.1 (by simpa using hp.2))
  inv_mem := by
    intro p hp
    have hp0 : p ≠ (0, 0) := by simpa using hp.2
    exact div_ne_zero (cuspCurve_snd_ne_zero hn hp.1 hp0) (cuspCurve_fst_ne_zero hn hp.1 hp0)

/-! ## Main theorem -/

/-- **Resolution of singularities for the curves `y ^ n = x ^ (n + 1)`,
in characteristic zero** (an explicit instance of Hironaka's theorem).

For a field `k` of characteristic `0` and `n ≥ 2`, the curve
`C_n = {(x, y) : y ^ n = x ^ (n + 1)} ⊆ 𝔸²` is singular exactly at the origin,
and the polynomial map `φ : 𝔸¹ → C_n`, `t ↦ (t ^ n, t ^ (n + 1))`, from the
smooth affine line is a resolution of singularities of `C_n`:

* the singular locus of `C_n`, computed by the Jacobian criterion, is exactly the
  origin (this is where characteristic zero is used);
* `φ` is a resolution of singularities of `C_n` in the sense of
  `Math2.IsPlaneCurveResolution`, with regular inverse `(x, y) ↦ y / x` over the
  smooth locus;
* explicitly: `φ` maps `𝔸¹` into `C_n`, is injective with image all of `C_n`
  (a bijective, finite, hence proper morphism), and restricts to a bijection
  `𝔸¹ ∖ {0} ≃ C_n ∖ {(0,0)}` inverted by `(x, y) ↦ y / x`. -/
