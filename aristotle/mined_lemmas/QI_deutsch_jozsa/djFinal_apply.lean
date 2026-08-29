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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

variable {n : ℕ}

/-- The computational basis of `n` qubits, indexed by bit strings `Fin n → Bool`. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- The all-zeros bit string. -/

theorem djFinal_apply (f : Bits n → Bool) (y : Bits n) :
    djFinal f y
      = ((2 : ℂ) ^ n)⁻¹ * ∑ x : Bits n, phaseSign x y * (if f x then (-1 : ℂ) else 1) := by
  have key : ∀ x : Bits n,
      phaseSign x y * phaseOracle f (hadamard (zeroState : Bits n → ℂ)) x
        = ((Real.sqrt 2 ^ n : ℝ) : ℂ)⁻¹ * (phaseSign x y * (if f x then (-1 : ℂ) else 1)) := by
    intro x
    simp only [phaseOracle]
    rw [hadamard_zeroState]
    ring
  show ((Real.sqrt 2 ^ n : ℝ) : ℂ)⁻¹ *
      ∑ x : Bits n, phaseSign x y *
        phaseOracle f (hadamard (zeroState : Bits n → ℂ)) x = _
  rw [Finset.sum_congr rfl (fun x _ => key x), ← Finset.mul_sum, ← mul_assoc, norm_const_sq]

/-- The amplitude of `|0…0⟩` in the final state is the normalised character sum of `f`. -/
