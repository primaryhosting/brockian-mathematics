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

