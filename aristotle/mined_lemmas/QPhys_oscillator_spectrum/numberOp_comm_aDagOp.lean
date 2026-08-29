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

theorem numberOp_comm_aDagOp : numberOp ∘ₗ aDagOp - aDagOp ∘ₗ numberOp = aDagOp := by
  refine Finsupp.lhom_ext' fun n => LinearMap.ext fun c => ?_
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, Finsupp.lsingle_apply,
    aDagOp_single, numberOp_single]
  rw [← Finsupp.single_sub]
  congr 1
  push_cast
  ring

/--
**Spectrum of the quantum harmonic oscillator.**

For the Hamiltonian `H = ℏω (a†a + 1/2)` built from the ladder operators `a`, `a†`
(which satisfy `[a, a†] = 1`, see `QPhys.ladder_ccr`) acting on the Fock space,
the set of eigenvalues of `H` is exactly `{ℏω (n + 1/2) : n ∈ ℕ}`.
-/
