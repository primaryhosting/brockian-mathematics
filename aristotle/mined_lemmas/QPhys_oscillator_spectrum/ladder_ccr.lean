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

theorem ladder_ccr : aOp ∘ₗ aDagOp - aDagOp ∘ₗ aOp = LinearMap.id := by
  refine Finsupp.lhom_ext' fun n => LinearMap.ext fun c => ?_
  cases n with
  | zero =>
      simp [aOp_single, aDagOp_single]
  | succ m =>
      have h1 : ((Real.sqrt (m + 1 + 1) : ℝ) : ℂ) * (((Real.sqrt (m + 1 + 1) : ℝ) : ℂ) * c)
          = ((m : ℂ) + 2) * c := by
        rw [← mul_assoc]
        have := sqrt_mul_self_cast (m + 2)
        push_cast at this ⊢
        rw [show ((m : ℝ) + 1 + 1) = ((m : ℝ) + 2) by ring, this]
      have h2 : ((Real.sqrt (m + 1) : ℝ) : ℂ) * (((Real.sqrt (m + 1) : ℝ) : ℂ) * c)
          = ((m : ℂ) + 1) * c := by
        rw [← mul_assoc]
        have := sqrt_mul_self_cast (m + 1)
        push_cast at this ⊢
        rw [this]
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
        Finsupp.lsingle_apply, aOp_single, aDagOp_single, Nat.succ_sub_one]
      push_cast
      rw [h1, h2, ← Finsupp.single_sub]
      ring_nf

