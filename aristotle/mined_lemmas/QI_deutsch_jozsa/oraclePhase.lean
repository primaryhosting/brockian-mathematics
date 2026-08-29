/-
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
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

namespace QI

open Finset

/-- The number of inputs `x` on which the oracle `f` returns `true`. -/

noncomputable def oraclePhase {n : ℕ} (f : (Fin n → Bool) → Bool)
    (psi : (Fin n → Bool) → ℝ) : (Fin n → Bool) → ℝ :=
  fun x => (if f x then (-1 : ℝ) else 1) * psi x

/-- The Deutsch–Jozsa circuit: start in `|0…0⟩`, apply `H^{⊗n}`, query the phase
oracle for `f` once, apply `H^{⊗n}` again. -/
