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

lemma isBalanced_id_one : IsBalancedFn (fun x : Fin 1 → Bool => x 0) := by
  simp only [IsBalancedFn]
  decide

/-- On one bit, the Deutsch–Jozsa circuit applied to `f x = x₀` never returns `0`. -/
example : djState (fun x : Fin 1 → Bool => x 0) (zeroStr 1) = 0 := by
  rw [djState_zeroStr]
  exact djAmp_of_balanced _ isBalanced_id_one

/-- Parity on two bits is balanced. -/
