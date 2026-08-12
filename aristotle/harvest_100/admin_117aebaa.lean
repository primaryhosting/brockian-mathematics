import Mathlib
/-!
# Robertson Uncertainty
Category: Quantum Computing
Target: QC.robertson_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` lines to precede every other command in a file
-- (a `/-! ... -/` module docstring is a command), so the required header comment
-- appears immediately after the single `import Mathlib` line.

open scoped ComplexConjugate

namespace QC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local notation "⟪" x ", " y "⟫" => (inner ℂ x y : ℂ)

/-- The expectation value `⟨A⟩_ψ = ⟪ψ, A ψ⟫` of an observable `A` in the state `ψ`
(a real number when `A` is self-adjoint and `ψ` is a unit vector). -/
noncomputable def mean (A : E →L[ℂ] E) (ψ : E) : ℝ := Complex.re ⟪ψ, A ψ⟫

/-- The standard deviation (uncertainty) `ΔA = ‖(A - ⟨A⟩) ψ‖` of an observable `A`
in the state `ψ`. -/
noncomputable def Delta (A : E →L[ℂ] E) (ψ : E) : ℝ :=
  ‖A ψ - ((mean A ψ : ℂ)) • ψ‖

/-- The commutator `[A, B] = AB - BA` of two observables. -/
noncomputable def commutator (A B : E →L[ℂ] E) : E →L[ℂ] E := A * B - B * A

/-- For a self-adjoint `A`, the expectation value `⟪ψ, A ψ⟫` is real. -/
theorem mean_ofReal {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) (ψ : E) :
    ((mean A ψ : ℝ) : ℂ) = ⟪ψ, A ψ⟫ := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  rw [mean, ← Complex.conj_eq_iff_re, inner_conj_symm]
  simpa using (hs ψ ψ)

/-- The inner product of the two centred vectors `(A - ⟨A⟩)ψ` and `(B - ⟨B⟩)ψ`. -/
theorem inner_shift {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {ψ : E} (hψ : ‖ψ‖ = 1) :
    ⟪A ψ - ((mean A ψ : ℂ)) • ψ, B ψ - ((mean B ψ : ℂ)) • ψ⟫
      = ⟪ψ, (A * B) ψ⟫ - ((mean A ψ : ℂ) * (mean B ψ : ℂ)) := by
  have hsA := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hAB : ⟪A ψ, B ψ⟫ = ⟪ψ, (A * B) ψ⟫ := by
    simpa using (hsA ψ (B ψ))
  have hAψ : ⟪A ψ, ψ⟫ = ((mean A ψ : ℂ)) := by
    rw [mean_ofReal hA]
    simpa using (hsA ψ ψ)
  have hBψ : ⟪ψ, B ψ⟫ = ((mean B ψ : ℂ)) := (mean_ofReal hB ψ).symm
  have hnn : ⟪ψ, ψ⟫ = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, hAB, hAψ, hBψ, hnn]
  ring

/-- For a self-adjoint `A` and a unit vector `ψ`, `(ΔA)² = ⟨A²⟩ - ⟨A⟩²`,
i.e. `Delta` is the square root of the usual quantum-mechanical variance. -/
theorem Delta_sq_eq_variance {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) {ψ : E} (hψ : ‖ψ‖ = 1) :
    (Delta A ψ) ^ 2 = Complex.re ⟪ψ, (A * A) ψ⟫ - (mean A ψ) ^ 2 := by
  have h := inner_shift hA hA hψ
  have h2 : Complex.re ⟪A ψ - ((mean A ψ : ℂ)) • ψ, A ψ - ((mean A ψ : ℂ)) • ψ⟫
      = (Delta A ψ) ^ 2 := by
    simpa [Delta] using inner_self_eq_norm_sq (𝕜 := ℂ) (A ψ - ((mean A ψ : ℂ)) • ψ)
  rw [← h2, h]
  simp [sq]

/-- For a complex number `z`, `‖z - conj z‖ = 2 |Im z| ≤ 2 ‖z‖`. -/
theorem norm_sub_conj_le (z : ℂ) : ‖z - conj z‖ ≤ 2 * ‖z‖ := by
  have hz : z - conj z = (2 * Complex.I) * ((z.im : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp
      ring
  rw [hz, norm_mul, norm_mul, Complex.norm_I]
  simpa using Complex.abs_im_le_norm z

/-- **Robertson uncertainty relation**: for observables (self-adjoint operators) `A`, `B`
and a unit state vector `ψ`, `ΔA · ΔB ≥ ½ |⟨[A, B]⟩|`. -/
theorem robertson_uncertainty {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {ψ : E} (hψ : ‖ψ‖ = 1) :
    Delta A ψ * Delta B ψ ≥ (1 / 2) * ‖⟪ψ, (commutator A B) ψ⟫‖ := by
  set x := A ψ - ((mean A ψ : ℂ)) • ψ with hx
  set y := B ψ - ((mean B ψ : ℂ)) • ψ with hy
  have h1 := inner_shift hA hB hψ
  have h2 := inner_shift hB hA hψ
  have hcomm : ⟪ψ, (commutator A B) ψ⟫ = ⟪x, y⟫ - ⟪y, x⟫ := by
    rw [h1, h2, commutator]
    simp
    ring
  have hconj : ⟪y, x⟫ = conj ⟪x, y⟫ := (inner_conj_symm y x).symm
  have hnorm : ‖⟪x, y⟫ - conj ⟪x, y⟫‖ ≤ 2 * ‖⟪x, y⟫‖ := norm_sub_conj_le _
  have hCS : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm x y
  rw [ge_iff_le, hcomm, hconj]
  have hxy : Delta A ψ * Delta B ψ = ‖x‖ * ‖y‖ := rfl
  rw [hxy]
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

