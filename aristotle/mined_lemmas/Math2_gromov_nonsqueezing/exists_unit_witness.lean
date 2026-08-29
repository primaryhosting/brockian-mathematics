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

/-! ## Setup: the standard symplectic vector space -/

/-- The standard symplectic phase space `ℝ^{2n}`, with coordinates indexed by `ι ⊕ ι`:
`Sum.inl i` is the `i`-th position coordinate `qᵢ`, and `Sum.inr i` the `i`-th momentum
coordinate `pᵢ`.  It carries the standard Euclidean inner product. -/
abbrev Phase (ι : Type*) [Fintype ι] := EuclideanSpace ℝ (ι ⊕ ι)

variable {ι : Type*} [Fintype ι]

/-- The standard symplectic form `ω(x, y) = ∑ᵢ (qᵢ(x) pᵢ(y) - pᵢ(x) qᵢ(y))`. -/

lemma exists_unit_witness {u v : Phase ι} (h : omegaForm u v = 1) :
    ∃ x : Phase ι, ‖x‖ = 1 ∧ 1 ≤ ⟪u, x⟫ ^ 2 + ⟪v, x⟫ ^ 2 := by
  have hu : u ≠ 0 := by
    rintro rfl
    rw [omegaForm_zero_left] at h
    exact zero_ne_one h
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hgram : 1 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 := one_le_gram_of_omegaForm_eq_one hu h
  by_cases hcase : 1 ≤ ‖u‖
  · refine ⟨‖u‖⁻¹ • u, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hun), inv_mul_cancel₀ hun.ne']
    · have : ⟪u, ‖u‖⁻¹ • u⟫ = ‖u‖ := by
        rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp
      rw [this]
      nlinarith [sq_nonneg (⟪v, ‖u‖⁻¹ • u⟫ : ℝ)]
  · push_neg at hcase
    set w : Phase ι := v - (⟪u, v⟫ / ‖u‖ ^ 2) • u with hw
    have h4 : ‖u‖ ^ 2 * ‖w‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 :=
      norm_sq_mul_norm_proj_sq u v hu
    have hw2 : 1 < ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    have hwn : 0 < ‖w‖ := by nlinarith [norm_nonneg w]
    refine ⟨‖w‖⁻¹ • w, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwn), inv_mul_cancel₀ hwn.ne']
    · have hu' : ⟪u, ‖w‖⁻¹ • w⟫ = 0 := by
        rw [real_inner_smul_right, hw, inner_proj_left u v hu]
        ring
      have hv' : ⟪v, ‖w‖⁻¹ • w⟫ = ‖w‖ := by
        rw [real_inner_smul_right, hw, inner_proj_right u v hu, ← hw]
        field_simp
      rw [hu', hv']
      nlinarith

/-! ## Gromov's nonsqueezing theorem (linear case) -/

/-- **Gromov's nonsqueezing theorem**, linear case.

If a linear symplectomorphism `A` of the standard symplectic vector space `ℝ^{2n}`
maps the open ball of radius `r > 0` into the open symplectic cylinder of radius `R ≥ 0`
over the `i₀`-th coordinate plane, then `r ≤ R`.  In other words, a symplectic linear map
can never squeeze a ball into a thinner cylinder, no matter how large the dimension. -/
