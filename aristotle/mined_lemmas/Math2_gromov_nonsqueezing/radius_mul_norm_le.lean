/-
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped RealInnerProductSpace

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

/-- The symplectic vector space `ℝ^{2n}`, modelled as the Euclidean space indexed by `ι ⊕ ι`:
the `Sum.inl` coordinates are the "positions" and the `Sum.inr` coordinates the "momenta". -/
abbrev SymplecticSpace (ι : Type*) [Fintype ι] : Type _ := EuclideanSpace ℝ (ι ⊕ ι)

variable {ι : Type*} [Fintype ι]

/-- The standard symplectic form on `ℝ^{2n} = ℝ^ι × ℝ^ι`,
`ω(u, v) = ∑ i, (u_i v_{n+i} - u_{n+i} v_i)`. -/

theorem radius_mul_norm_le (r R : ℝ) (hR : 0 ≤ R) (w : SymplecticSpace ι)
    (h : ∀ x : SymplecticSpace ι, ‖x‖ < r → (symplecticForm x w) ^ 2 < R ^ 2) :
    r * ‖w‖ ≤ R := by
  by_contra hcon
  push_neg at hcon
  have hw : 0 < ‖w‖ := by
    rcases (norm_nonneg w).lt_or_eq with h' | h'
    · exact h'
    · exfalso; rw [← h'] at hcon; simp at hcon; linarith
  set t : ℝ := R / ‖w‖ with ht
  have ht0 : 0 ≤ t := div_nonneg hR hw.le
  have htr : t < r := by
    rw [ht, div_lt_iff₀ hw]
    linarith [hcon]
  set x : SymplecticSpace ι := (t / ‖w‖) • cxStructure w with hx
  have hxnorm : ‖x‖ = t := by
    rw [hx, norm_smul, norm_cxStructure]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg ht0 hw.le)]
    field_simp
  have hval : symplecticForm x w = R := by
    rw [symplecticForm_eq_inner, hx, real_inner_smul_left, real_inner_self_eq_norm_sq,
      norm_cxStructure]
    rw [ht]
    field_simp
  have := h x (by rw [hxnorm]; exact htr)
  rw [hval] at this
  linarith

@[simp]
