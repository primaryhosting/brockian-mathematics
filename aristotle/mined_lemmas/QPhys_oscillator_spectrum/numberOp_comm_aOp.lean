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

theorem numberOp_comm_aOp : numberOp ∘ₗ aOp - aOp ∘ₗ numberOp = -aOp := by
  refine Finsupp.lhom_ext' fun n => LinearMap.ext fun c => ?_
  cases n with
  | zero => simp [aOp_single, numberOp_single]
  | succ m =>
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.neg_apply,
        Finsupp.lsingle_apply, aOp_single, numberOp_single, Nat.succ_sub_one]
      rw [← Finsupp.single_sub, ← Finsupp.single_neg]
      congr 1
      push_cast
      ring

/-- `[N, a†] = a†`: the creation operator raises the number eigenvalue by one. -/
