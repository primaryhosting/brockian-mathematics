/-
# Robertson Uncertainty
Category: Quantum Computing
Target: QC.robertson_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped InnerProductSpace ComplexConjugate

namespace QC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An *observable* is a symmetric (self-adjoint) linear operator on a complex
inner product space. -/
def IsObservable (A : E →ₗ[ℂ] E) : Prop := ∀ x y, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ

/-- The expectation value `⟨A⟩ψ = ⟪ψ, A ψ⟫` of an operator `A` in the state `ψ`. -/
noncomputable def expect (A : E →ₗ[ℂ] E) (ψ : E) : ℂ := ⟪ψ, A ψ⟫_ℂ

/-- The standard deviation `ΔA = ‖(A - ⟨A⟩) ψ‖` of an operator `A` in the state `ψ`. -/
noncomputable def Delta (A : E →ₗ[ℂ] E) (ψ : E) : ℝ := ‖A ψ - expect A ψ • ψ‖

/-- The commutator `[A, B] = A B - B A`. -/
noncomputable def commutator (A B : E →ₗ[ℂ] E) : E →ₗ[ℂ] E := A ∘ₗ B - B ∘ₗ A

@[simp] lemma commutator_apply (A B : E →ₗ[ℂ] E) (x : E) :
    commutator A B x = A (B x) - B (A x) := rfl

/-- The expectation value of an observable is real. -/
lemma conj_expect {A : E →ₗ[ℂ] E} (hA : IsObservable A) (ψ : E) :
    conj (expect A ψ) = expect A ψ := by
  unfold expect
  rw [inner_conj_symm, hA]

/-- For a normalized state, the inner product of the two centred vectors
`(A - ⟨A⟩)ψ` and `(B - ⟨B⟩)ψ` equals `⟪ψ, A B ψ⟫ - ⟨A⟩⟨B⟩`. -/
lemma inner_centred {A : E →ₗ[ℂ] E} (hA : IsObservable A) (B : E →ₗ[ℂ] E)
    {ψ : E} (hψ : ‖ψ‖ = 1) :
    ⟪A ψ - expect A ψ • ψ, B ψ - expect B ψ • ψ⟫_ℂ
      = ⟪ψ, A (B ψ)⟫_ℂ - expect A ψ * expect B ψ := by
  have hAψ : ⟪A ψ, ψ⟫_ℂ = ⟪ψ, A ψ⟫_ℂ := hA _ _
  have hABψ : ⟪A ψ, B ψ⟫_ℂ = ⟪ψ, A (B ψ)⟫_ℂ := hA _ _
  simp only [expect]
  simp [hAψ, hABψ, hψ]
  ring

/-- **Robertson uncertainty relation.**  For observables `A`, `B` (symmetric linear
operators on a complex inner product space) and a normalized state `ψ`, the product of
the standard deviations is at least half the modulus of the expectation of the
commutator:  `ΔA · ΔB ≥ ½ |⟨[A, B]⟩|`. -/
theorem robertson_uncertainty {A B : E →ₗ[ℂ] E} (hA : IsObservable A) (hB : IsObservable B)
    {ψ : E} (hψ : ‖ψ‖ = 1) :
    Delta A ψ * Delta B ψ ≥ ‖expect (commutator A B) ψ‖ / 2 := by
  set f : E := A ψ - expect A ψ • ψ with hf
  set g : E := B ψ - expect B ψ • ψ with hg
  set z : ℂ := ⟪f, g⟫_ℂ with hz
  -- the expectation of the commutator is `z - conj z`
  have key : expect (commutator A B) ψ = z - conj z := by
    have h1 : z = ⟪ψ, A (B ψ)⟫_ℂ - expect A ψ * expect B ψ := inner_centred hA B hψ
    have h2 : ⟪g, f⟫_ℂ = ⟪ψ, B (A ψ)⟫_ℂ - expect B ψ * expect A ψ := inner_centred hB A hψ
    have h3 : conj z = ⟪g, f⟫_ℂ := by rw [hz, inner_conj_symm]
    simp only [expect, commutator_apply, inner_sub_right]
    rw [h3, h2, h1]
    simp only [expect]
    ring
  -- `z - conj z = 2 i Im z`, hence its norm is `2 |Im z| ≤ 2 ‖z‖`
  have hnorm : ‖z - conj z‖ ≤ 2 * ‖z‖ := by
    simp only [Complex.sub_conj, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_two]
    have : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    linarith
  have hcs : ‖z‖ ≤ ‖f‖ * ‖g‖ := norm_inner_le_norm (𝕜 := ℂ) f g
  have : ‖expect (commutator A B) ψ‖ ≤ 2 * (Delta A ψ * Delta B ψ) := by
    rw [key]
    calc ‖z - conj z‖ ≤ 2 * ‖z‖ := hnorm
      _ ≤ 2 * (‖f‖ * ‖g‖) := by linarith
      _ = 2 * (Delta A ψ * Delta B ψ) := by rw [Delta, Delta, ← hf, ← hg]
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

