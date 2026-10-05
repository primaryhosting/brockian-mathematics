/-
# Dft Inversion
Category: Characters
Target: Brockian.Characters5.dft_inversion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Dft Inversion
Category: Characters
Target: Brockian.Characters5.dft_inversion
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

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/

lemma sum_e : ∑ b : ZMod 5, e b = 0 := by
  show ∑ b : Fin 5, e b = 0
  rw [Fin.sum_univ_five]
  have h0 : e (0 : Fin 5) = 1 := by simp [e]
  have h1 : e (1 : Fin 5) = ω := by
    show ω ^ (1 : ZMod 5).val = ω
    rw [show (1 : ZMod 5).val = 1 from rfl, pow_one]
  have h2 : e (2 : Fin 5) = ω ^ 2 := by show ω ^ (2 : ZMod 5).val = ω ^ 2; rfl
  have h3 : e (3 : Fin 5) = ω ^ 3 := by show ω ^ (3 : ZMod 5).val = ω ^ 3; rfl
  have h4 : e (4 : Fin 5) = ω ^ 4 := by show ω ^ (4 : ZMod 5).val = ω ^ 4; rfl
  rw [h0, h1, h2, h3, h4]
  exact sum_omega_pow

