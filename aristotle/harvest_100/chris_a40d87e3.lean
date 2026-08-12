import Mathlib
/-!
# Robertson Uncertainty
Category: Quantum Computing
Target: QC.robertson_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` to be the very first command of a module,
so the mandated header comment is placed immediately after the single `import Mathlib` line.
-/

namespace QC

open scoped ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The expectation value `⟪ψ, A ψ⟫` of an observable `A` in the state `ψ`. -/
noncomputable def expect (A : E →ₗ[ℂ] E) (ψ : E) : ℂ := inner ℂ ψ (A ψ)

/-- The observable `A` centered at its expectation value in the state `ψ`,
i.e. `A - ⟨A⟩ • id`. -/
noncomputable def centered (A : E →ₗ[ℂ] E) (ψ : E) : E →ₗ[ℂ] E :=
  A - (expect A ψ) • LinearMap.id

/-- The variance of the observable `A` in the state `ψ`:
the real part of `⟪ψ, (A - ⟨A⟩)² ψ⟫`. -/
noncomputable def variance (A : E →ₗ[ℂ] E) (ψ : E) : ℝ :=
  (inner ℂ ψ (centered A ψ (centered A ψ ψ))).re

/-- The standard deviation (uncertainty) `ΔA` of the observable `A` in the state `ψ`. -/
noncomputable def Delta (A : E →ₗ[ℂ] E) (ψ : E) : ℝ := Real.sqrt (variance A ψ)

/-- For a symmetric operator the expectation value is real. -/
lemma conj_expect_of_isSymmetric {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric) (ψ : E) :
    conj (expect A ψ) = expect A ψ := by
  rw [expect, inner_conj_symm]
  exact hA ψ ψ

/-- The centered observable is again symmetric. -/
lemma centered_isSymmetric {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric) (ψ : E) :
    (centered A ψ).IsSymmetric := by
  intro x y
  simp only [centered, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    conj_expect_of_isSymmetric hA ψ, hA x y]

/-- The variance is the squared norm of `(A - ⟨A⟩) ψ`. -/
lemma variance_eq_norm_sq {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric) (ψ : E) :
    variance A ψ = ‖centered A ψ ψ‖ ^ 2 := by
  have h := (centered_isSymmetric hA ψ) ψ (centered A ψ ψ)
  rw [variance, ← h]
  simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (centered A ψ ψ)

/-- `ΔA = ‖(A - ⟨A⟩) ψ‖`. -/
lemma Delta_eq_norm {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric) (ψ : E) :
    Delta A ψ = ‖centered A ψ ψ‖ := by
  rw [Delta, variance_eq_norm_sq hA ψ, Real.sqrt_sq (norm_nonneg _)]

/-- Centering does not change the commutator. -/
lemma centered_commutator (A B : E →ₗ[ℂ] E) (ψ : E) :
    centered A ψ ∘ₗ centered B ψ - centered B ψ ∘ₗ centered A ψ = A ∘ₗ B - B ∘ₗ A := by
  ext x
  simp only [centered, LinearMap.coe_comp, Function.comp_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, LinearMap.map_sub, LinearMap.map_smul]
  abel_nf
  module

/-- The expectation of the commutator equals `⟪u, v⟫ - ⟪v, u⟫` where `u = (A - ⟨A⟩)ψ`,
`v = (B - ⟨B⟩)ψ`. -/
lemma inner_commutator_eq {A B : E →ₗ[ℂ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric) (ψ : E) :
    inner ℂ ψ ((A ∘ₗ B - B ∘ₗ A) ψ)
      = inner ℂ (centered A ψ ψ) (centered B ψ ψ)
        - conj (inner ℂ (centered A ψ ψ) (centered B ψ ψ)) := by
  rw [← centered_commutator A B ψ]
  rw [inner_conj_symm]
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply, inner_sub_right]
  rw [← (centered_isSymmetric hA ψ) ψ (centered B ψ ψ),
    ← (centered_isSymmetric hB ψ) ψ (centered A ψ ψ)]

/-- **Robertson uncertainty relation.** For symmetric (self-adjoint) observables `A`, `B`
and any state `ψ`, the product of the uncertainties `ΔA · ΔB` is at least
`½ |⟨[A, B]⟩|`. -/
theorem robertson_uncertainty {A B : E →ₗ[ℂ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (ψ : E) :
    Delta A ψ * Delta B ψ ≥ ‖inner ℂ ψ ((A ∘ₗ B - B ∘ₗ A) ψ)‖ / 2 := by
  set u := centered A ψ ψ with hu
  set v := centered B ψ ψ with hv
  have key : ‖inner ℂ ψ ((A ∘ₗ B - B ∘ₗ A) ψ)‖ ≤ 2 * (‖u‖ * ‖v‖) := by
    rw [inner_commutator_eq hA hB ψ]
    calc ‖(inner ℂ u v : ℂ) - conj (inner ℂ u v)‖
        ≤ ‖(inner ℂ u v : ℂ)‖ + ‖conj (inner ℂ u v : ℂ)‖ := norm_sub_le _ _
      _ = 2 * ‖(inner ℂ u v : ℂ)‖ := by rw [RCLike.norm_conj]; ring
      _ ≤ 2 * (‖u‖ * ‖v‖) := by
          have := norm_inner_le_norm (𝕜 := ℂ) u v
          linarith
  rw [Delta_eq_norm hA ψ, Delta_eq_norm hB ψ, ← hu, ← hv, ge_iff_le, div_le_iff₀ (by norm_num)]
  linarith

end QC

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

