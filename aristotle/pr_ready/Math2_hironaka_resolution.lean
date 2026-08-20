/-!
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Statement: Resolution of singularities in characteristic 0 (Hironaka; statement).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math2

/-- The affine cuspidal cubic `{(x, y) | y ^ 2 = x ^ 3}` over a field `k`. -/
def cuspCurve (k : Type*) [Field k] : Set (k × k) := {p : k × k | p.2 ^ 2 = p.1 ^ 3}

/-- The resolution (normalization) map of the cuspidal cubic: the affine line, which is
smooth, mapped onto the cuspidal cubic by `t ↦ (t ^ 2, t ^ 3)`. -/
def cuspRes (k : Type*) [Field k] : k → k × k := fun t => (t ^ 2, t ^ 3)

/-- The rational inverse of `cuspRes`, regular away from the singular point. -/
def cuspRes.inv (k : Type*) [Field k] : k × k → k := fun p => p.2 / p.1

variable {k : Type*} [Field k]

lemma cuspRes_mem (t : k) : cuspRes k t ∈ cuspCurve k := by
  simp [cuspRes, cuspCurve]
  ring

lemma cuspRes_inv_cuspRes (t : k) : cuspRes.inv k (cuspRes k t) = t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [cuspRes, cuspRes.inv]
  · simp only [cuspRes, cuspRes.inv]
    rw [div_eq_iff (pow_ne_zero 2 ht)]
    ring

lemma cuspRes_injective : Function.Injective (cuspRes k) :=
  Function.LeftInverse.injective cuspRes_inv_cuspRes

/-- Key lemma: every point of the cuspidal cubic is in the image of the resolution map,
with the explicit preimage `y / x` (and `0` at the singular point). -/
lemma cuspRes_cuspRes_inv {p : k × k} (hp : p ∈ cuspCurve k) :
    cuspRes k (cuspRes.inv k p) = p := by
  obtain ⟨x, y⟩ := p
  simp only [cuspCurve, Set.mem_setOf_eq] at hp
  rcases eq_or_ne x 0 with rfl | hx
  · have hy : y = 0 := by
      have : y ^ 2 = 0 := by simpa using hp
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    simp [cuspRes, cuspRes.inv, hy]
  · have hx2 : x ^ 2 ≠ 0 := pow_ne_zero _ hx
    have hx3 : x ^ 3 ≠ 0 := pow_ne_zero _ hx
    refine Prod.ext ?_ ?_ <;> simp only [cuspRes, cuspRes.inv] <;> field_simp
    · exact hp
    · calc y ^ 3 = y * y ^ 2 := by ring
        _ = y * x ^ 3 := by rw [hp]

lemma cuspRes_surjOn : Set.SurjOn (cuspRes k) Set.univ (cuspCurve k) := by
  intro p hp
  exact ⟨cuspRes.inv k p, Set.mem_univ _, cuspRes_cuspRes_inv hp⟩

lemma cuspRes_bijOn : Set.BijOn (cuspRes k) Set.univ (cuspCurve k) :=
  ⟨fun t _ => cuspRes_mem t, Set.injOn_of_injective cuspRes_injective, cuspRes_surjOn⟩

/-- The singular locus of the cuspidal cubic (in characteristic `0`) is exactly the origin:
the gradient `(-3 x ^ 2, 2 y)` of `y ^ 2 - x ^ 3` vanishes at a point of the curve iff that
point is the origin. -/
lemma cusp_singular_locus [CharZero k] {p : k × k} (hp : p ∈ cuspCurve k) :
    (3 * p.1 ^ 2 = 0 ∧ 2 * p.2 = 0) ↔ p = (0, 0) := by
  obtain ⟨x, y⟩ := p
  simp only [cuspCurve, Set.mem_setOf_eq] at hp
  constructor
  · rintro ⟨h1, h2⟩
    have hx : x = 0 := by
      have : x ^ 2 = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · norm_num at h
        · exact h
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    have hy : y = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · norm_num at h
      · exact h
    simp [hx, hy]
  · rintro h
    obtain ⟨hx, hy⟩ := Prod.mk.injEq .. ▸ h
    simp_all

/-- **Resolution of singularities (Hironaka), an instance in characteristic 0.**

Over any field of characteristic zero, the singular cuspidal cubic `C : y ^ 2 = x ^ 3`
admits a resolution by the smooth affine line: the morphism `t ↦ (t ^ 2, t ^ 3)`

* is a bijection from the (smooth) affine line onto `C`;
* is an isomorphism over the smooth locus `C \ {(0,0)}`, with regular inverse `(x, y) ↦ y / x`;
* and `C` is genuinely singular exactly at the origin (the gradient of the defining
  equation vanishes there and nowhere else on `C`).
-/
theorem hironaka_resolution (k : Type*) [Field k] [CharZero k] :
    Set.BijOn (cuspRes k) Set.univ (cuspCurve k) ∧
      (∀ p ∈ cuspCurve k, cuspRes k (cuspRes.inv k p) = p) ∧
      (∀ t : k, cuspRes.inv k (cuspRes k t) = t) ∧
      (∀ p ∈ cuspCurve k, ((3 * p.1 ^ 2 = 0 ∧ 2 * p.2 = 0) ↔ p = (0, 0))) := by
  refine ⟨cuspRes_bijOn, fun p hp => cuspRes_cuspRes_inv hp, fun t => cuspRes_inv_cuspRes t,
    fun p hp => cusp_singular_locus hp⟩

/-- Over the reals the resolution map is in addition proper (indeed a closed embedding),
so it is a proper birational morphism, as in Hironaka's theorem. -/
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
theorem hironaka_resolution_closedEmbedding_real :
    Topology.IsClosedEmbedding (cuspRes ℝ) ∧ Set.range (cuspRes ℝ) = cuspCurve ℝ := by
  have hcont : Continuous (cuspRes ℝ) := by
    unfold cuspRes; fun_prop
  refine ⟨Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hcont
    cuspRes_injective hironaka_resolution_proper_real.isClosedMap, ?_⟩
  apply Set.Subset.antisymm
  · rintro p ⟨t, rfl⟩
    exact cuspRes_mem t
  · intro p hp
    exact ⟨cuspRes.inv ℝ p, cuspRes_cuspRes_inv hp⟩

end Math2

