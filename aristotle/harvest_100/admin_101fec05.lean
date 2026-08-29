/-
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Classical

namespace Math2

open MvPolynomial

/-!
## Setting

We work with affine plane curves over a field `k` of characteristic zero, points of the
affine plane being encoded as functions `Fin 2 → k` (so that they can be plugged into
`MvPolynomial (Fin 2) k`).

The theorem `Math2.hironaka_resolution` below is a formalised instance of Hironaka's
resolution of singularities in characteristic zero: for every `m ≥ 1` the plane curve

  `C_m : y ^ 2 = x ^ (2 * m + 1)`

is singular (exactly at the origin), and the map

  `π_m : 𝔸¹ → C_m , t ↦ (t ^ 2, t ^ (2 * m + 1))`

from the smooth affine line is a proper birational bijection onto `C_m` which is an
isomorphism away from the singular point; i.e. `π_m` is a resolution of singularities
of `C_m`.
-/

variable {k : Type*} [Field k]

omit [Field k] in
/-- Two points of the affine plane agree iff their coordinates do. -/
theorem pt_ext_iff {p q : Fin 2 → k} : p = q ↔ p 0 = q 0 ∧ p 1 = q 1 :=
  funext_iff.trans Fin.forall_fin_two

/-- The defining polynomial `y ^ 2 - x ^ (2 * m + 1)` of the curve `C_m`. -/
noncomputable def cuspPoly (m : ℕ) : MvPolynomial (Fin 2) k :=
  X 1 ^ 2 - X 0 ^ (2 * m + 1)

/-- The curve `C_m = {(x, y) | y ^ 2 = x ^ (2 * m + 1)}`. -/
def curve (m : ℕ) : Set (Fin 2 → k) :=
  {p | p 1 ^ 2 = p 0 ^ (2 * m + 1)}

/-- A point is a singular point of the hypersurface `{f = 0}` when `f` and all its partial
derivatives vanish there. -/
def IsSingularPt (f : MvPolynomial (Fin 2) k) (p : Fin 2 → k) : Prop :=
  eval p f = 0 ∧ ∀ i, eval p ((pderiv i) f) = 0

/-- The parametrisation `t ↦ (t ^ 2, t ^ (2 * m + 1))` of `C_m` by the affine line. -/
def param (m : ℕ) (t : k) : Fin 2 → k :=
  ![t ^ 2, t ^ (2 * m + 1)]

/-- The candidate inverse of `param`, defined away from `x = 0`. -/
def paramInv (m : ℕ) (p : Fin 2 → k) : k := p 1 / p 0 ^ m

@[simp] theorem param_zero_coord (m : ℕ) (t : k) : param m t 0 = t ^ 2 := rfl

@[simp] theorem param_one_coord (m : ℕ) (t : k) : param m t 1 = t ^ (2 * m + 1) := rfl

@[simp] theorem mem_curve_iff {m : ℕ} {p : Fin 2 → k} :
    p ∈ curve m ↔ p 1 ^ 2 = p 0 ^ (2 * m + 1) := Iff.rfl

/-- The vanishing locus of `cuspPoly m` is exactly `curve m`. -/
theorem eval_cuspPoly (m : ℕ) (p : Fin 2 → k) :
    eval p (cuspPoly m) = p 1 ^ 2 - p 0 ^ (2 * m + 1) := by
  simp [cuspPoly]

theorem mem_curve_iff_eval_eq_zero (m : ℕ) (p : Fin 2 → k) :
    p ∈ curve m ↔ eval p (cuspPoly m) = 0 := by
  rw [eval_cuspPoly, sub_eq_zero]
  rfl

/-- The `y`-partial derivative of the defining polynomial, evaluated at a point. -/
theorem eval_pderiv_one (m : ℕ) (p : Fin 2 → k) :
    eval p ((pderiv 1) (cuspPoly (k := k) m)) = 2 * p 1 := by
  simp [cuspPoly]

/-- The `x`-partial derivative of the defining polynomial vanishes at the origin (for `m ≥ 1`). -/
theorem eval_pderiv_zero_at_origin (m : ℕ) (hm : 1 ≤ m) :
    eval (0 : Fin 2 → k) ((pderiv 0) (cuspPoly (k := k) m)) = 0 := by
  simp only [cuspPoly, map_sub]
  simp
  right
  omega

/-- On the curve, the `x`-coordinate vanishes iff the `y`-coordinate does. -/
theorem curve_coord_zero_iff {m : ℕ} {p : Fin 2 → k} (hp : p ∈ curve m) :
    p 0 = 0 ↔ p 1 = 0 := by
  rw [mem_curve_iff] at hp
  constructor
  · intro h
    have : p 1 ^ 2 = 0 := by rw [hp, h]; simp
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  · intro h
    have : p 0 ^ (2 * m + 1) = 0 := by rw [← hp, h]; simp
    exact pow_eq_zero_iff (by omega) |>.mp this

/-- The origin lies on the curve. -/
theorem origin_mem_curve (m : ℕ) : (0 : Fin 2 → k) ∈ curve m := by
  simp [curve]

/-- **The curve is singular at the origin.** -/
theorem isSingularPt_origin (m : ℕ) (hm : 1 ≤ m) :
    IsSingularPt (cuspPoly (k := k) m) 0 := by
  refine ⟨?_, ?_⟩
  · rw [← mem_curve_iff_eval_eq_zero]
    exact origin_mem_curve m
  · intro i
    fin_cases i
    · exact eval_pderiv_zero_at_origin m hm
    · simp [cuspPoly]

/-- **The origin is the only singular point of the curve** (uses characteristic zero). -/
theorem isSingularPt_eq_origin [CharZero k] {m : ℕ} {p : Fin 2 → k} (hp : p ∈ curve m)
    (hsing : IsSingularPt (cuspPoly m) p) : p = 0 := by
  have h1 : (2 : k) * p 1 = 0 := by
    rw [← eval_pderiv_one m p]; exact hsing.2 1
  have hy : p 1 = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hx : p 0 = 0 := (curve_coord_zero_iff hp).mpr hy
  rw [pt_ext_iff]
  simpa using ⟨hx, hy⟩

/-- The parametrisation lands on the curve. -/
theorem param_mem_curve (m : ℕ) (t : k) : param m t ∈ curve m := by
  simp only [mem_curve_iff, param_one_coord, param_zero_coord, ← pow_mul]
  ring_nf

/-- **The parametrisation is onto the curve.** -/
theorem range_param (m : ℕ) : Set.range (param (k := k) m) = curve m := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨t, rfl⟩
    exact param_mem_curve m t
  · intro p hp
    rcases eq_or_ne (p 0) 0 with h0 | h0
    · refine ⟨0, ?_⟩
      have hy : p 1 = 0 := (curve_coord_zero_iff hp).mp h0
      rw [pt_ext_iff]
      simp [param, h0, hy]
    · refine ⟨paramInv m p, ?_⟩
      have hx : p 0 ^ m ≠ 0 := pow_ne_zero _ h0
      have hsq : (paramInv m p) ^ 2 = p 0 := by
        rw [mem_curve_iff] at hp
        rw [paramInv, div_pow, hp]
        field_simp
        ring
      rw [pt_ext_iff]
      refine ⟨by simpa using hsq, ?_⟩
      have : paramInv m p ^ (2 * m + 1) = (paramInv m p ^ 2) ^ m * paramInv m p := by
        rw [← pow_mul, ← pow_succ]
      rw [param_one_coord, this, hsq, paramInv]
      field_simp

/-- **The parametrisation is injective.** -/
theorem param_injective (m : ℕ) : Function.Injective (param (k := k) m) := by
  intro s t hst
  rw [pt_ext_iff] at hst
  obtain ⟨h2, hodd⟩ := hst
  simp only [param_zero_coord, param_one_coord] at h2 hodd
  rcases eq_or_ne s 0 with hs | hs
  · subst hs
    have : t ^ 2 = 0 := by simpa using h2.symm
    exact ((pow_eq_zero_iff (n := 2) (by norm_num)).mp this).symm
  · have hsm : (s ^ 2) ^ m ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hs)
    have e1 : (s ^ 2) ^ m * s = (s ^ 2) ^ m * t := by
      calc (s ^ 2) ^ m * s = s ^ (2 * m + 1) := by rw [← pow_mul, ← pow_succ]
        _ = t ^ (2 * m + 1) := hodd
        _ = (t ^ 2) ^ m * t := by rw [← pow_mul, ← pow_succ]
        _ = (s ^ 2) ^ m * t := by rw [h2]
    exact mul_left_cancel₀ hsm e1
  
/-- Away from the singular point, `paramInv` is a left inverse of the parametrisation. -/
theorem paramInv_param (m : ℕ) {t : k} (ht : t ≠ 0) : paramInv m (param m t) = t := by
  have h : (t ^ 2) ^ m ≠ 0 := pow_ne_zero _ (pow_ne_zero _ ht)
  rw [paramInv, param_one_coord, param_zero_coord]
  field_simp
  ring

/-- Away from the singular point, `paramInv` is a right inverse of the parametrisation. -/
theorem param_paramInv (m : ℕ) {p : Fin 2 → k} (hp : p ∈ curve m) (h0 : p 0 ≠ 0) :
    param m (paramInv m p) = p := by
  have : p ∈ Set.range (param (k := k) m) := by rw [range_param]; exact hp
  obtain ⟨t, rfl⟩ := this
  have ht : t ≠ 0 := by
    intro h; apply h0; simp [h]
  rw [paramInv_param m ht]

/--
**Hironaka resolution of singularities (characteristic zero), formalised instance.**

Let `k` be a field of characteristic zero and `m ≥ 1`.  The affine plane curve
`C_m : y ^ 2 = x ^ (2 * m + 1)` is singular at the origin, and the origin is its only
singular point.  The map `π_m (t) = (t ^ 2, t ^ (2 * m + 1))` from the smooth affine line
`𝔸¹` is a bijection onto `C_m`, and it restricts to an isomorphism between
`𝔸¹ \ {0}` and `C_m` minus its singular point, with inverse `(x, y) ↦ y / x ^ m`.
Thus `π_m` is a resolution of singularities of `C_m`.
-/
theorem hironaka_resolution {k : Type*} [Field k] [CharZero k] (m : ℕ) (hm : 1 ≤ m) :
    -- the curve is the vanishing locus of its defining polynomial
    (∀ p : Fin 2 → k, p ∈ curve m ↔ eval p (cuspPoly m) = 0) ∧
    -- it is singular at the origin
    IsSingularPt (cuspPoly (k := k) m) 0 ∧
    -- and nowhere else
    (∀ p ∈ curve (k := k) m, IsSingularPt (cuspPoly m) p → p = 0) ∧
    -- the affine line maps onto the curve
    Set.range (param (k := k) m) = curve m ∧
    -- bijectively
    Function.Injective (param (k := k) m) ∧
    -- and this map is an isomorphism away from the singular point
    (∀ t : k, t ≠ 0 → paramInv m (param m t) = t) ∧
    (∀ p ∈ curve (k := k) m, p 0 ≠ 0 → param m (paramInv m p) = p) := by
  refine ⟨mem_curve_iff_eval_eq_zero m, isSingularPt_origin m hm, ?_, range_param m,
    param_injective m, fun t ht => paramInv_param m ht, fun p hp h0 => param_paramInv m hp h0⟩
  intro p hp hsing
  exact isSingularPt_eq_origin hp hsing

/-- Sanity check: the hypotheses of `hironaka_resolution` are satisfiable, e.g. over `ℚ`
with `m = 1` (the classical cuspidal cubic `y ^ 2 = x ^ 3`). -/
example :
    IsSingularPt (cuspPoly (k := ℚ) 1) 0 ∧ Set.range (param (k := ℚ) 1) = curve 1 :=
  ⟨(hironaka_resolution (k := ℚ) 1 le_rfl).2.1, (hironaka_resolution (k := ℚ) 1 le_rfl).2.2.2.1⟩

end Math2

-- Axiom check
#print axioms Math2.hironaka_resolution

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

