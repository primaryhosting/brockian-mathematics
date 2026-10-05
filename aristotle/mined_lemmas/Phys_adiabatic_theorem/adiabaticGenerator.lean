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

noncomputable def adiabaticGenerator (τ : ℝ) (H P dP : ℝ → (E →L[ℂ] E)) (s : ℝ) : E →L[ℂ] E :=
  (-(Complex.I * (τ : ℂ))) • H s + katoGenerator P dP s

/-- Uniqueness for the linear ODE `X' = G X` in a Banach algebra: a solution vanishing at `0`
vanishes identically.  (Proved by Grönwall's inequality, forwards and backwards in time.) -/
