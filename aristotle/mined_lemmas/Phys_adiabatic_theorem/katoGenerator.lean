/-
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
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

namespace Phys

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Kato's geometric generator `K(s) = [P'(s), P(s)] = P'(s)P(s) - P(s)P'(s)` associated with a
differentiable family of spectral projections `P` with derivative `dP`. -/

noncomputable def katoGenerator (P dP : ℝ → (E →L[ℂ] E)) (s : ℝ) : E →L[ℂ] E :=
  dP s * P s - P s * dP s

/-- The generator of the adiabatic evolution at slowness parameter `τ`:
`G(s) = -i τ H(s) + K(s)`, the dynamical part plus Kato's geometric part. -/
