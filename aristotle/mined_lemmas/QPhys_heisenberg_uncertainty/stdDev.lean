/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace QPhys

open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value `⟨A⟩_ψ = ⟪ψ, A ψ⟫` of an observable `A` in the state `ψ`. -/

noncomputable def stdDev (A : H →ₗ[ℂ] H) (ψ : H) : ℝ := ‖A ψ - expectation A ψ • ψ‖

/-- If the "commutator" `⟪u,v⟫ - ⟪v,u⟫` equals `c * i` for a real `c`, then
`c/2 ≤ ‖u‖ * ‖v‖`.  This is the Cauchy–Schwarz half of the uncertainty principle. -/
