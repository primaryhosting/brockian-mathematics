/-
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

/-!
## The Deutsch–Jozsa circuit

We model the `n`-qubit register by its (real) amplitude vector, a function
`(Fin n → Bool) → ℝ`, indexed by bit strings.  The circuit is

`|0…0⟩  --H^{⊗n}-->  --U_f (phase kickback)-->  --H^{⊗n}-->  measure`.

Everything below is stated for real amplitudes, which suffices because all gates
involved (Hadamard and the phase oracle) have real matrix entries.
-/

/-- The all-zeros bit string. -/

lemma djState_apply {n : ℕ} (f : (Fin n → Bool) → Bool) (y : Fin n → Bool) :
    djState f y = ((2 : ℝ) ^ n)⁻¹ * ∑ x : Fin n → Bool, signIP x y * phase (f x) := by
  rw [djState, hadamard_basisVec_zero, hadamard]
  have hstep : ∀ x : Fin n → Bool,
      signIP x y * phaseOracle f (fun _ => ((Real.sqrt 2) ^ n)⁻¹) x
        = ((Real.sqrt 2) ^ n)⁻¹ * (signIP x y * phase (f x)) := by
    intro x
    rw [phaseOracle]
    ring
  rw [Finset.sum_congr rfl fun x _ => hstep x, ← Finset.mul_sum, ← mul_assoc, ← mul_inv,
    sqrt_two_pow_mul_self]

/-- The all-zeros amplitude of the circuit output is exactly `2⁻ⁿ ∑ₓ (-1)^{f x}`. -/
