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

lemma sum_phase {n : ℕ} (f : (Fin n → Bool) → Bool) :
    ∑ x : Fin n → Bool, phase (f x) =
      (2 : ℝ) ^ n - 2 * (Finset.univ.filter fun x : Fin n → Bool => f x = true).card := by
  have h : ∀ x : Fin n → Bool,
      phase (f x) = 1 - 2 * (if f x = true then (1 : ℝ) else 0) := by
    intro x
    by_cases hx : f x = true <;> norm_num [phase, hx]
  rw [Finset.sum_congr rfl fun x _ => h x]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
  simp

/-- The amplitude in terms of the number of `true` inputs. -/
