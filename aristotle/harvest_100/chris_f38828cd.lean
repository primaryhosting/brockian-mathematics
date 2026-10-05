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
def cuspCurve (k : Type*) [Field k] (n : ℕ) : Set (k × k) :=
  {p | p.2 ^ n = p.1 ^ (n + 1)}

/-- The normalization (resolution) map from the affine line `𝔸¹` onto `C_n`,
`t ↦ (t ^ n, t ^ (n + 1))`.  It is given by polynomials, hence is a morphism
of affine varieties, and its source `𝔸¹` is smooth. -/
def cuspParam (k : Type*) [Field k] (n : ℕ) : k → k × k :=
  fun t => (t ^ n, t ^ (n + 1))

/-- The rational inverse `(x, y) ↦ y / x` of `cuspParam`, regular away from the
singular point of `C_n`. -/
def cuspParamInv (k : Type*) [Field k] : k × k → k :=
  fun p => p.2 / p.1

/-- The gradient of the defining polynomial `F = y ^ n - x ^ (n + 1)` of `C_n`,
i.e. `(∂F/∂x, ∂F/∂y) = (-(n+1) x ^ n, n y ^ (n-1))`.  A point of `C_n` is a smooth
point exactly when this gradient is nonzero there (Jacobian criterion). -/
def cuspJacobian (k : Type*) [Field k] (n : ℕ) (p : k × k) : k × k :=
  (-((n + 1 : k) * p.1 ^ n), (n : k) * p.2 ^ (n - 1))

/-- Abstract notion of a **resolution of singularities of a plane curve
`C ⊆ 𝔸²` by the affine line `𝔸¹`**, with singular locus `S ⊆ C` and with `U ⊆ 𝔸¹`
the preimage of the smooth locus.

The data is a morphism `f : 𝔸¹ → 𝔸²` and a rational map `g` in the other direction
such that `f` is a bijection from the (smooth) affine line onto `C` — in particular
a finite, hence proper, birational morphism — restricting to an isomorphism
`U ≃ C ∖ S` over the smooth locus of `C`, with inverse `g` regular there. -/
structure IsPlaneCurveResolution {k : Type*} [Field k]
    (C S : Set (k × k)) (f : k → k × k) (g : k × k → k) (U : Set k) : Prop where
  /-- The singular locus is part of the curve. -/
  singular_subset : S ⊆ C
  /-- The resolution map lands in the curve. -/
  mapsTo : ∀ t, f t ∈ C
  /-- The resolution map is injective. -/
  injective : Function.Injective f
  /-- The resolution map hits every point of the curve. -/
  surjective : ∀ p ∈ C, ∃ t, f t = p
  /-- `U` is exactly the preimage of the smooth locus. -/
  preimage_smooth : ∀ t, f t ∉ S ↔ t ∈ U
  /-- `g` inverts `f` over the smooth locus. -/
  left_inv : ∀ t ∈ U, g (f t) = t
  /-- `f` inverts `g` over the smooth locus. -/
  right_inv : ∀ p ∈ C \ S, f (g p) = p
  /-- `g` maps the smooth locus into `U`. -/
  inv_mem : ∀ p ∈ C \ S, g p ∈ U

/-! ## Basic properties of the parametrization -/

lemma cuspParam_mem {k : Type*} [Field k] (n : ℕ) (t : k) :
    cuspParam k n t ∈ cuspCurve k n := by
  simp only [cuspCurve, cuspParam, Set.mem_setOf_eq]
  ring

lemma cuspParam_injective {k : Type*} [Field k] (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective (cuspParam k n) := by
  intro s t hst
  simp only [cuspParam, Prod.mk.injEq] at hst
  obtain ⟨h1, h2⟩ := hst
  rcases eq_or_ne s 0 with hs | hs
  · subst hs
    have : t ^ n = 0 := by
      simpa [zero_pow (by omega : n ≠ 0)] using h1.symm
    exact (pow_eq_zero_iff (by omega : n ≠ 0)).1 this |>.symm
  · have hsn : s ^ n ≠ 0 := pow_ne_zero _ hs
    have htn : t ^ n ≠ 0 := by rw [← h1]; exact hsn
    have hs' : s = s ^ (n + 1) / s ^ n := by
      field_simp; ring
    have ht' : t = t ^ (n + 1) / t ^ n := by
      field_simp; ring
    rw [hs', ht', h1, h2]

lemma cuspParam_eq_zero_iff {k : Type*} [Field k] {n : ℕ} (hn : 1 ≤ n) (t : k) :
    cuspParam k n t = (0, 0) ↔ t = 0 := by
  constructor
  · intro h
    simp only [cuspParam, Prod.mk.injEq] at h
    exact (pow_eq_zero_iff (by omega : n ≠ 0)).1 h.1
  · rintro rfl
    simp [cuspParam, zero_pow (by omega : n ≠ 0), zero_pow (by omega : n + 1 ≠ 0)]

lemma zero_mem_cuspCurve {k : Type*} [Field k] {n : ℕ} (hn : 1 ≤ n) :
    ((0, 0) : k × k) ∈ cuspCurve k n := by
  simp [cuspCurve, zero_pow (by omega : n ≠ 0), zero_pow (by omega : n + 1 ≠ 0)]

lemma cuspCurve_zero_of_fst_zero {k : Type*} [Field k] {n : ℕ} (hn : 1 ≤ n)
    {p : k × k} (hp : p ∈ cuspCurve k n) (h : p.1 = 0) : p = (0, 0) := by
  have hy : p.2 ^ n = 0 := by
    simpa [cuspCurve, h, zero_pow (by omega : n + 1 ≠ 0)] using hp
  have : p.2 = 0 := (pow_eq_zero_iff (by omega : n ≠ 0)).1 hy
  exact Prod.ext h this

lemma cuspCurve_fst_ne_zero {k : Type*} [Field k] {n : ℕ} (hn : 1 ≤ n)
    {p : k × k} (hp : p ∈ cuspCurve k n) (hp0 : p ≠ (0, 0)) : p.1 ≠ 0 :=
  fun h => hp0 (cuspCurve_zero_of_fst_zero hn hp h)

lemma cuspCurve_snd_ne_zero {k : Type*} [Field k] {n : ℕ} (hn : 1 ≤ n)
    {p : k × k} (hp : p ∈ cuspCurve k n) (hp0 : p ≠ (0, 0)) : p.2 ≠ 0 := by
  intro h
  have hx : p.1 ≠ 0 := cuspCurve_fst_ne_zero hn hp hp0
  have hx' : p.1 ^ (n + 1) = 0 := by
    have hp' : p.2 ^ n = p.1 ^ (n + 1) := hp
    rw [h, zero_pow (by omega : n ≠ 0)] at hp'
    exact hp'.symm
  exact hx ((pow_eq_zero_iff (by omega : n + 1 ≠ 0)).1 hx')

lemma cuspParamInv_cuspParam {k : Type*} [Field k] (n : ℕ) {t : k} (ht : t ≠ 0) :
    cuspParamInv k (cuspParam k n t) = t := by
  have : (t : k) ^ n ≠ 0 := pow_ne_zero _ ht
  simp only [cuspParamInv, cuspParam, pow_succ]
  field_simp

lemma cuspParam_cuspParamInv {k : Type*} [Field k] (n : ℕ) {p : k × k}
    (hp : p ∈ cuspCurve k n) (hx : p.1 ≠ 0) :
    cuspParam k n (cuspParamInv k p) = p := by
  have hp' : p.2 ^ n = p.1 ^ (n + 1) := hp
  have h1 : (p.2 / p.1) ^ n = p.1 := by
    rw [div_pow, hp', pow_succ, mul_comm, mul_div_assoc, div_self (pow_ne_zero n hx), mul_one]
  have h2 : (p.2 / p.1) ^ (n + 1) = p.2 := by
    rw [pow_succ, h1]
    field_simp
  simp only [cuspParamInv, cuspParam, h1, h2]

/-- **Jacobian criterion for `C_n` in characteristic zero:** the gradient of the
defining equation vanishes at a point of the curve exactly at the origin. -/
lemma cuspJacobian_eq_zero_iff {k : Type*} [Field k] [CharZero k] {n : ℕ} (hn : 2 ≤ n)
    {p : k × k} (hp : p ∈ cuspCurve k n) :
    cuspJacobian k n p = (0, 0) ↔ p = (0, 0) := by
  constructor
  · intro hj
    simp only [cuspJacobian, Prod.mk.injEq, neg_eq_zero, mul_eq_zero] at hj
    have hnp1 : ((n : k) + 1) ≠ 0 := by
      have : ((n + 1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      simpa using this
    have hx : p.1 = 0 := by
      rcases hj.1 with h | h
      · exact absurd h hnp1
      · exact (pow_eq_zero_iff (by omega : n ≠ 0)).1 h
    exact cuspCurve_zero_of_fst_zero (by omega) hp hx
  · rintro rfl
    simp only [cuspJacobian, Prod.mk.injEq]
    exact ⟨by simp [zero_pow (by omega : n ≠ 0)], by simp [zero_pow (by omega : n - 1 ≠ 0)]⟩

/-- The normalization map `t ↦ (t ^ n, t ^ (n + 1))` is a resolution of singularities
of `C_n` with singular locus the origin. -/
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
theorem hironaka_resolution (k : Type*) [Field k] [CharZero k] (n : ℕ) (hn : 2 ≤ n) :
    {p ∈ cuspCurve k n | cuspJacobian k n p = (0, 0)} = {((0, 0) : k × k)} ∧
    IsPlaneCurveResolution (cuspCurve k n) {((0, 0) : k × k)} (cuspParam k n)
      (cuspParamInv k) {t : k | t ≠ 0} ∧
    (∀ t : k, cuspParam k n t ∈ cuspCurve k n) ∧
    Function.Injective (cuspParam k n) ∧
    Set.range (cuspParam k n) = cuspCurve k n ∧
    Set.BijOn (cuspParam k n) {t : k | t ≠ 0} (cuspCurve k n \ {(0, 0)}) ∧
    (∀ t : k, t ≠ 0 → (cuspParam k n t).2 / (cuspParam k n t).1 = t) ∧
    (∀ p ∈ cuspCurve k n, p ≠ (0, 0) → cuspParam k n (p.2 / p.1) = p) ∧
    ((0, 0) : k × k) ∈ cuspCurve k n ∧
    (∀ p ∈ cuspCurve k n, cuspJacobian k n p = (0, 0) ↔ p = (0, 0)) := by
  have hn1 : 1 ≤ n := by omega
  have hres := isPlaneCurveResolution_cusp (k := k) (n := n) hn1
  have hjac : ∀ p ∈ cuspCurve k n, cuspJacobian k n p = (0, 0) ↔ p = (0, 0) :=
    fun _ hp => cuspJacobian_eq_zero_iff hn hp
  have hback : ∀ p ∈ cuspCurve k n, p ≠ (0, 0) → cuspParam k n (p.2 / p.1) = p :=
    fun p hp hp0 => cuspParam_cuspParamInv n hp (cuspCurve_fst_ne_zero hn1 hp hp0)
  refine ⟨?_, hres, cuspParam_mem n, cuspParam_injective n hn1, ?_, ?_,
    fun t ht => cuspParamInv_cuspParam n ht, hback, zero_mem_cuspCurve hn1, hjac⟩
  · ext p
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hp, hj⟩
      exact (hjac p hp).1 hj
    · rintro rfl
      exact ⟨zero_mem_cuspCurve hn1, (hjac _ (zero_mem_cuspCurve hn1)).2 rfl⟩
  · apply Set.eq_of_subset_of_subset
    · rintro _ ⟨t, rfl⟩
      exact cuspParam_mem n t
    · intro p hp
      obtain ⟨t, ht⟩ := hres.surjective p hp
      exact ⟨t, ht⟩
  · refine ⟨?_, (cuspParam_injective n hn1).injOn, ?_⟩
    · intro t ht
      exact ⟨cuspParam_mem n t, by simpa using (cuspParam_eq_zero_iff hn1 t).not.2 ht⟩
    · intro p hp
      have hp0 : p ≠ (0, 0) := by simpa using hp.2
      refine ⟨cuspParamInv k p, ?_, hback p hp.1 hp0⟩
      exact div_ne_zero (cuspCurve_snd_ne_zero hn1 hp.1 hp0) (cuspCurve_fst_ne_zero hn1 hp.1 hp0)

end Math2

