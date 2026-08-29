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

theorem djState_of_constant {n : ℕ} (f : (Fin n → Bool) → Bool) (h : IsConstantFn f)
    (y : Fin n → Bool) :
    djState f y = phase (f (zeroStr n)) * (if y = zeroStr n then 1 else 0) := by
  have hpow : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  have hconst : ∀ x : Fin n → Bool, phase (f x) = phase (f (zeroStr n)) := by
    intro x; rw [h x (zeroStr n)]
  rw [djState_apply, Finset.sum_congr rfl fun x _ => by rw [hconst x], ← Finset.sum_mul,
    sum_signIP]
  by_cases hy : y = zeroStr n
  · rw [if_pos hy, if_pos hy, ← mul_assoc, inv_mul_cancel₀ hpow]
    ring
  · rw [if_neg hy, if_neg hy]
    ring

/-- If `f` is constant, the all-zeros amplitude has modulus `1`: the measurement returns
the all-zeros string with probability one, so the algorithm correctly reports "constant". -/
