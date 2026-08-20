/-
# Robertson Uncertainty
Category: Quantum Computing
Target: QC.robertson_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An operator `A` on a complex inner product space is *symmetric* (an observable) if
`⟪A x, y⟫ = ⟪x, A y⟫` for all `x, y`. -/
def IsSymmetricOp (A : H →ₗ[ℂ] H) : Prop := ∀ x y : H, inner ℂ (A x) y = inner ℂ x (A y)

/-- The expectation value `⟨A⟩_ψ = ⟪ψ, A ψ⟫` of an operator `A` in the state `ψ`. -/
noncomputable def expect (A : H →ₗ[ℂ] H) (ψ : H) : ℂ := inner ℂ ψ (A ψ)

/-- The standard deviation (uncertainty) `ΔA = ‖(A - ⟨A⟩) ψ‖` of an operator `A`
in the state `ψ`. -/
noncomputable def stddev (A : H →ₗ[ℂ] H) (ψ : H) : ℝ := ‖A ψ - expect A ψ • ψ‖

/-- The commutator `[A, B] = A B - B A`. -/
noncomputable def commutator (A B : H →ₗ[ℂ] H) : H →ₗ[ℂ] H := A ∘ₗ B - B ∘ₗ A

/-- Expectation values of symmetric operators are real. -/
lemma expect_conj (A : H →ₗ[ℂ] H) (hA : IsSymmetricOp A) (ψ : H) :
    (starRingEnd ℂ) (expect A ψ) = expect A ψ := by
  unfold expect
  rw [inner_conj_symm, hA]

/-- For a unit state, `(ΔA)^2 = ⟨A²⟩ - ⟨A⟩²`, i.e. the definition of `stddev`
agrees with the usual variance formula. -/
lemma stddev_sq (A : H →ₗ[ℂ] H) (hA : IsSymmetricOp A) (ψ : H) (hψ : ‖ψ‖ = 1) :
    ((stddev A ψ : ℂ)) ^ 2 = expect (A ∘ₗ A) ψ - (expect A ψ) ^ 2 := by
  have hnorm : (inner ℂ ψ ψ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
  have ha : (starRingEnd ℂ) (expect A ψ) = expect A ψ := expect_conj A hA ψ
  have h1 : ((stddev A ψ : ℂ)) ^ 2
      = (inner ℂ (A ψ - expect A ψ • ψ) (A ψ - expect A ψ • ψ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have h2 : (inner ℂ (A ψ) ψ : ℂ) = expect A ψ := by
    rw [← ha]; unfold expect; rw [inner_conj_symm]
  have h4 : (inner ℂ (A ψ) (A ψ) : ℂ) = expect (A ∘ₗ A) ψ := by
    unfold expect; rw [hA]; rfl
  rw [h1, inner_sub_left, inner_sub_right, inner_sub_right, inner_smul_left, inner_smul_left,
    inner_smul_right, inner_smul_right, h2, hnorm, ha, h4]
  show _ = _
  unfold expect
  ring

/-- **Robertson uncertainty relation.**  For observables (symmetric operators) `A`, `B`
on a complex inner product space and a unit state `ψ`,
`ΔA · ΔB ≥ ½ |⟨[A, B]⟩|`. -/
theorem robertson_uncertainty (A B : H →ₗ[ℂ] H)
    (hA : IsSymmetricOp A) (hB : IsSymmetricOp B) (ψ : H) (hψ : ‖ψ‖ = 1) :
    stddev A ψ * stddev B ψ ≥ (1 / 2) * ‖expect (commutator A B) ψ‖ := by
  set a : ℂ := expect A ψ with ha_def
  set b : ℂ := expect B ψ with hb_def
  have ha : (starRingEnd ℂ) a = a := expect_conj A hA ψ
  have hb : (starRingEnd ℂ) b = b := expect_conj B hB ψ
  have hnorm : (inner ℂ ψ ψ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
  set u : H := A ψ - a • ψ with hu_def
  set v : H := B ψ - b • ψ with hv_def
  have haψ : (inner ℂ (A ψ) ψ : ℂ) = a := by
    rw [← ha, ha_def]; unfold expect; rw [inner_conj_symm]
  have hbψ : (inner ℂ (B ψ) ψ : ℂ) = b := by
    rw [← hb, hb_def]; unfold expect; rw [inner_conj_symm]
  -- the commutator expectation equals `⟪u,v⟫ - ⟪v,u⟫`
  have key : expect (commutator A B) ψ = inner ℂ u v - inner ℂ v u := by
    have huv : (inner ℂ u v : ℂ) = inner ℂ (A ψ) (B ψ) - a * b := by
      rw [hu_def, hv_def, inner_sub_left, inner_sub_right, inner_sub_right, inner_smul_left,
        inner_smul_left, inner_smul_right, inner_smul_right, haψ, hnorm, ha]
      have h : (inner ℂ ψ (B ψ) : ℂ) = b := by rw [← inner_conj_symm, hbψ, hb]
      rw [h]; ring
    have hvu : (inner ℂ v u : ℂ) = inner ℂ (B ψ) (A ψ) - b * a := by
      rw [hu_def, hv_def, inner_sub_left, inner_sub_right, inner_sub_right, inner_smul_left,
        inner_smul_left, inner_smul_right, inner_smul_right, hbψ, hnorm, hb]
      have h : (inner ℂ ψ (A ψ) : ℂ) = a := by rw [← inner_conj_symm, haψ, ha]
      rw [h]; ring
    rw [huv, hvu]
    have hc : expect (commutator A B) ψ
        = (inner ℂ ψ (A (B ψ)) : ℂ) - inner ℂ ψ (B (A ψ)) := by
      unfold expect commutator
      simp
    rw [hc, ← hA ψ (B ψ), ← hB ψ (A ψ)]
    ring
  -- `⟪v,u⟫` is the conjugate of `⟪u,v⟫`
  have hconj : (inner ℂ v u : ℂ) = (starRingEnd ℂ) (inner ℂ u v) := by
    rw [inner_conj_symm]
  have hbound : ‖expect (commutator A B) ψ‖ ≤ 2 * ‖(inner ℂ u v : ℂ)‖ := by
    rw [key, hconj]
    calc ‖(inner ℂ u v : ℂ) - (starRingEnd ℂ) (inner ℂ u v)‖
        ≤ ‖(inner ℂ u v : ℂ)‖ + ‖(starRingEnd ℂ) (inner ℂ u v)‖ := norm_sub_le _ _
      _ = 2 * ‖(inner ℂ u v : ℂ)‖ := by rw [RCLike.norm_conj]; ring
  have hCS : ‖(inner ℂ u v : ℂ)‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  have : ‖expect (commutator A B) ψ‖ ≤ 2 * (stddev A ψ * stddev B ψ) := by
    refine hbound.trans ?_
    have : ‖(inner ℂ u v : ℂ)‖ ≤ stddev A ψ * stddev B ψ := hCS
    linarith
  linarith

end QC

