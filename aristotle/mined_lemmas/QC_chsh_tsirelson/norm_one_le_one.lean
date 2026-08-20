/-
# Chsh Tsirelson
Category: Quantum Computing
Target: QC.chsh_tsirelson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Chsh Tsirelson
Category: Quantum Computing
Target: QC.chsh_tsirelson
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

namespace QC

section Algebraic

variable {R : Type*} [Ring R]

/-- The CHSH operator associated to four observables. -/

theorem norm_one_le_one : ‖(1 : A)‖ ≤ 1 := by
  have h : ‖(1 : A)‖ * ‖(1 : A)‖ = ‖(1 : A)‖ := by
    have := CStarRing.norm_star_mul_self (x := (1 : A))
    simpa [sq] using this.symm
  nlinarith [norm_nonneg (1 : A)]

/-- A self-adjoint involution in a C*-ring has norm at most `1`. -/
