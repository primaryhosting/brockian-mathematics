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

theorem abs_djAmp_of_constant {n : ℕ} (f : (Fin n → Bool) → Bool) (h : IsConstantFn f) :
    |djAmp f| = 1 := by
  rw [← djState_zeroStr, djState_of_constant f h, if_pos rfl, mul_one]
  cases hb : f (zeroStr n) <;> norm_num [phase]

/-!
## Deutsch–Jozsa
-/

/-- **Deutsch–Jozsa.**  Let `f : {0,1}ⁿ → {0,1}` satisfy the promise that it is either
constant or balanced.  Running the Deutsch–Jozsa circuit — a Hadamard layer, a **single**
query to the oracle for `f`, and a second Hadamard layer, applied to `|0…0⟩` — and measuring
in the computational basis decides which case holds:

* the amplitude of the all-zeros outcome is `2⁻ⁿ ∑ₓ (-1)^{f x}`;
* it is nonzero exactly when `f` is constant, in which case its modulus (hence the
  probability of observing `0…0`) is `1`;
* it is zero exactly when `f` is balanced, i.e. `0…0` is then never observed.

So one query suffices. -/
