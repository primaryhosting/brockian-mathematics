/-
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QPhys

noncomputable section

/-- The (algebraic) Fock space of the one–dimensional quantum harmonic oscillator:
finitely supported complex combinations of the number states `|n⟩`, `n : ℕ`. -/
abbrev Fock := ℕ →₀ ℂ

/-- The number state `|n⟩`. -/

def aOp : Fock →ₗ[ℂ] Fock :=
  Finsupp.lsum ℂ fun n =>
    LinearMap.toSpanSingleton ℂ Fock (Finsupp.single (n - 1) ((Real.sqrt n : ℝ) : ℂ))

/-- The creation (raising) ladder operator: `a† |n⟩ = √(n+1) |n+1⟩`. -/
