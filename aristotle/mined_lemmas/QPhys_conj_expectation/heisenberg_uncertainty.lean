/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace
open Matrix

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

set_option grind.warning false

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The spread (standard deviation) of the observable `A` in the state `psi`:
the norm of `A psi` after subtracting its mean value `⟪psi, A psi⟫ • psi`. -/

theorem heisenberg_uncertainty
    {X P : H →ₗ[ℂ] H} (hX : IsSymmetricOp X) (hP : IsSymmetricOp P)
    {hbar : ℝ} {psi : H} (hpsi : ‖psi‖ = 1)
    (hcomm : X (P psi) - P (X psi) = (Complex.I * (hbar : ℂ)) • psi) :
    spread X psi * spread P psi ≥ hbar / 2 :=
  le_trans (by linarith [le_abs_self hbar]) (heisenberg_uncertainty_abs hX hP hpsi hcomm)

/-! ### The hypotheses are satisfiable and the bound is sharp

On `ℂ²` the Pauli matrices `σₓ`, `σ_y` are symmetric and satisfy `[σₓ, σ_y] e₀ = 2i e₀`,
with both spreads equal to `1`, so equality holds in the uncertainty relation with `ℏ = 2`. -/

/-- The Pauli `σₓ` matrix as an operator on `ℂ²`, playing the role of the position observable. -/
