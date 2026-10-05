import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
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

set_option grind.warning false

namespace QI

variable {n : ℕ}

/-- The sign `(-1)^b` attached to a Boolean value. -/

lemma djState_zeroStr (f : (Fin n → Bool) → Bool) :
    djState f (zeroStr n) = ((2 ^ n : ℝ) : ℂ)⁻¹ * ∑ x : Fin n → Bool, sign (f x) := by
  have h1 : ∀ x : Fin n → Bool, phaseOracle f (hadamard (initState n)) x
      = sign (f x) * hcoeff n := by
    intro x; simp [phaseOracle, hadamard_initState]
  calc djState f (zeroStr n)
      = hcoeff n * ∑ x : Fin n → Bool, chi x (zeroStr n)
          * (phaseOracle f (hadamard (initState n)) x) := rfl
    _ = hcoeff n * ∑ x : Fin n → Bool, sign (f x) * hcoeff n := by
        refine congrArg _ (Finset.sum_congr rfl ?_)
        intro x _; rw [chi_zeroStr_right, one_mul, h1]
    _ = (hcoeff n * hcoeff n) * ∑ x : Fin n → Bool, sign (f x) := by
        rw [← Finset.sum_mul]; ring
    _ = ((2 ^ n : ℝ) : ℂ)⁻¹ * ∑ x : Fin n → Bool, sign (f x) := by rw [hcoeff_sq]

