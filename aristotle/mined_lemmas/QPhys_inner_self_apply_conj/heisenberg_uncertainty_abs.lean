/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring, so the header
-- above is repeated as a module docstring immediately after the import.)

import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open scoped ComplexConjugate InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value of a symmetric operator in a state is real. -/

theorem heisenberg_uncertainty_abs
    (X P : H →ₗ[ℂ] H) (hbar : ℝ) (psi : H)
    (hX : ∀ u v : H, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ)
    (hP : ∀ u v : H, ⟪P u, v⟫_ℂ = ⟪u, P v⟫_ℂ)
    (hcomm : ∀ u : H, X (P u) - P (X u) = (Complex.I * hbar) • u)
    (hnorm : ‖psi‖ = 1) :
    ‖X psi - ⟪psi, X psi⟫_ℂ • psi‖ * ‖P psi - ⟪psi, P psi⟫_ℂ • psi‖ ≥ |hbar| / 2 := by
  have h₁ : ‖X psi - ⟪psi, X psi⟫_ℂ • psi‖ * ‖P psi - ⟪psi, P psi⟫_ℂ • psi‖ ≥ hbar / 2 :=
    heisenberg_uncertainty X P hbar psi hX hP hcomm hnorm
  have hcomm' : ∀ u : H, P (X u) - X (P u) = (Complex.I * (-hbar : ℝ)) • u := by
    intro u
    have h := hcomm u
    have hneg : (Complex.I * ((-hbar : ℝ) : ℂ)) • u = -((Complex.I * (hbar : ℂ)) • u) := by
      rw [← neg_smul]
      push_cast
      ring_nf
    rw [hneg, ← h]
    abel
  have h₂ : ‖P psi - ⟪psi, P psi⟫_ℂ • psi‖ * ‖X psi - ⟪psi, X psi⟫_ℂ • psi‖ ≥ (-hbar) / 2 :=
    heisenberg_uncertainty P X (-hbar) psi hP hX hcomm' hnorm
  rcases abs_cases hbar with ⟨h, _⟩ | ⟨h, _⟩
  · rw [ge_iff_le, h]; exact h₁
  · rw [ge_iff_le, h, mul_comm]; exact h₂

end QPhys

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

