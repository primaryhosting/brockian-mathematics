/-
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is a plain block comment; it is repeated as a module
-- docstring immediately after the imports.)

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

/-- The `±1` phase attached to a boolean value: `sgn b = (-1)^b`. -/

lemma djAmp_of_isBalanced {n : ℕ} {f : (Fin n → Bool) → Bool} (hf : IsBalanced f) :
    djAmp f = 0 := by
  classical
  have hr : 2 * ((Finset.univ.filter fun x : Fin n → Bool => f x = true).card : ℝ)
      = (2 : ℝ) ^ n := by
    have := congrArg (fun m : ℕ => (m : ℝ)) hf
    push_cast at this
    simpa using this
  rw [djAmp_eq, sum_sgn, hr]
  simp

/--
**Deutsch–Jozsa.**  Given the promise that `f : (Fin n → Bool) → Bool` is either constant
or balanced, the single-query Deutsch–Jozsa circuit decides which: the all-zeros outcome
of `H^{⊗n} U_f H^{⊗n} |0…0⟩` has amplitude of modulus `1` exactly when `f` is constant,
and amplitude `0` exactly when `f` is balanced.  Hence one query to the oracle suffices.
-/
