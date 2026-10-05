import Mathlib
/-!
# Robertson Uncertainty
Category: Quantum Computing
Target: QC.robertson_uncertainty
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

set_option grind.warning false

namespace QC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An operator `A` is *symmetric* (a quantum observable) when
`⟪A x, y⟫ = ⟪x, A y⟫` for all `x, y`.  On a complete space this is exactly
self-adjointness. -/
def IsObservable (A : E →L[ℂ] E) : Prop := ∀ x y : E, inner ℂ (A x) y = inner ℂ x (A y)

/-- The expectation value `⟨A⟩_ψ = ⟪ψ, A ψ⟫` of an operator in a state. -/
noncomputable def expect (A : E →L[ℂ] E) (ψ : E) : ℂ := inner ℂ ψ (A ψ)

/-- The standard deviation (uncertainty) `ΔA = ‖(A - ⟨A⟩) ψ‖` of an operator in a state. -/
noncomputable def Delta (A : E →L[ℂ] E) (ψ : E) : ℝ := ‖A ψ - expect A ψ • ψ‖

/-- The commutator `[A, B] = A B - B A`. -/
noncomputable def comm (A B : E →L[ℂ] E) : E →L[ℂ] E := A * B - B * A

/-- The expectation value of an observable is real. -/
lemma expect_conj (A : E →L[ℂ] E) (hA : IsObservable A) (ψ : E) :
    (starRingEnd ℂ) (expect A ψ) = expect A ψ := by
  unfold expect
  rw [inner_conj_symm]
  exact hA ψ ψ

/-- `Δ A` really is the square root of the variance:
`(ΔA)^2 = ⟨(A - ⟨A⟩)^2⟩`. -/
lemma Delta_sq_eq_variance (A : E →L[ℂ] E) (hA : IsObservable A) (ψ : E) :
    ((Delta A ψ : ℂ)) ^ 2 =
      expect ((A - expect A ψ • (1 : E →L[ℂ] E)) * (A - expect A ψ • (1 : E →L[ℂ] E))) ψ := by
  set c : ℂ := expect A ψ with hc
  set S : E →L[ℂ] E := A - c • (1 : E →L[ℂ] E) with hS
  have hSapp : ∀ x : E, S x = A x - c • x := by
    intro x; simp [hS]
  have hSsymm : ∀ x y : E, inner ℂ (S x) y = inner ℂ x (S y) := by
    intro x y
    rw [hSapp, hSapp]
    rw [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hA x y,
      expect_conj A hA ψ]
  have : expect (S * S) ψ = inner ℂ (S ψ) (S ψ) := by
    unfold expect
    rw [hSsymm ψ (S ψ)]
    rfl
  rw [this, inner_self_eq_norm_sq_to_K]
  rfl

/-- **Robertson uncertainty relation.**

Mathlib does not contain this statement; the analytic input is the Cauchy-Schwarz
inequality `norm_inner_le_norm : ‖inner 𝕜 x y‖ ≤ ‖x‖ * ‖y‖`, applied to the
centred vectors `u = (A - ⟨A⟩)ψ` and `v = (B - ⟨B⟩)ψ`, together with the identity
`⟨[A,B]⟩ = ⟪u, v⟫ - ⟪v, u⟫`.
  For observables `A`, `B` and a unit state `ψ`,
`ΔA · ΔB ≥ ½ |⟨[A, B]⟩|`. -/
theorem robertson_uncertainty (A B : E →L[ℂ] E) (hA : IsObservable A) (hB : IsObservable B)
    (ψ : E) (hψ : ‖ψ‖ = 1) :
    ‖expect (comm A B) ψ‖ / 2 ≤ Delta A ψ * Delta B ψ := by
  set a : ℂ := expect A ψ with ha
  set b : ℂ := expect B ψ with hb
  set u : E := A ψ - a • ψ with hu
  set v : E := B ψ - b • ψ with hv
  have hψψ : (inner ℂ ψ ψ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
  have hAψψ : (inner ℂ (A ψ) ψ : ℂ) = a := by
    rw [hA ψ ψ]; rfl
  have hBψψ : (inner ℂ (B ψ) ψ : ℂ) = b := by
    rw [hB ψ ψ]; rfl
  have hca : (starRingEnd ℂ) a = a := expect_conj A hA ψ
  have hcb : (starRingEnd ℂ) b = b := expect_conj B hB ψ
  -- ⟪u, v⟫ = ⟨A B⟩ - a b
  have huv : (inner ℂ u v : ℂ) = expect (A * B) ψ - a * b := by
    rw [hu, hv, inner_sub_left, inner_sub_right, inner_sub_right,
      inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right,
      hca, hAψψ, hψψ, hA ψ (B ψ)]
    have : (inner ℂ ψ (B ψ) : ℂ) = b := rfl
    rw [this]
    have : expect (A * B) ψ = inner ℂ ψ (A (B ψ)) := rfl
    rw [this]
    ring
  have hvu : (inner ℂ v u : ℂ) = expect (B * A) ψ - b * a := by
    rw [hu, hv, inner_sub_left, inner_sub_right, inner_sub_right,
      inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right,
      hcb, hBψψ, hψψ, hB ψ (A ψ)]
    have : (inner ℂ ψ (A ψ) : ℂ) = a := rfl
    rw [this]
    have : expect (B * A) ψ = inner ℂ ψ (B (A ψ)) := rfl
    rw [this]
    ring
  have hkey : expect (comm A B) ψ = (inner ℂ u v : ℂ) - inner ℂ v u := by
    rw [huv, hvu]
    have : expect (comm A B) ψ = expect (A * B) ψ - expect (B * A) ψ := by
      unfold expect comm
      simp
    rw [this]
    ring
  have hbound : ‖expect (comm A B) ψ‖ ≤ 2 * (Delta A ψ * Delta B ψ) := by
    rw [hkey]
    calc ‖(inner ℂ u v : ℂ) - inner ℂ v u‖
        ≤ ‖(inner ℂ u v : ℂ)‖ + ‖(inner ℂ v u : ℂ)‖ := norm_sub_le _ _
      _ ≤ ‖u‖ * ‖v‖ + ‖v‖ * ‖u‖ := by
          gcongr <;> exact norm_inner_le_norm _ _
      _ = 2 * (Delta A ψ * Delta B ψ) := by
          rw [Delta, Delta, ← hu, ← hv]; ring
  linarith

/-- Robertson's relation in the literal `≥` form:  `ΔA · ΔB ≥ ½ |⟨[A, B]⟩|`. -/
theorem robertson_uncertainty' (A B : E →L[ℂ] E) (hA : IsObservable A) (hB : IsObservable B)
    (ψ : E) (hψ : ‖ψ‖ = 1) :
    Delta A ψ * Delta B ψ ≥ (1 / 2 : ℝ) * ‖expect (comm A B) ψ‖ := by
  have := robertson_uncertainty A B hA hB ψ hψ
  linarith

end QC

#print axioms QC.robertson_uncertainty
#print axioms QC.robertson_uncertainty'

