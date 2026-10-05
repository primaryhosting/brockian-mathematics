import Mathlib

/-!
# Deutsch Correct
Category: Quantum Computing
Target: QC.deutsch_correct
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

/-! ## The two-qubit state space

A two-qubit state is described by its amplitude function `Bool × Bool → ℂ`,
where `(x, y)` denotes the computational basis state `|x⟩ ⊗ |y⟩`
(with `false = 0` and `true = 1`). -/

/-- The sign `(-1)^b`. -/

noncomputable def hadamardFirst (psi : Bool × Bool → ℂ) : Bool × Bool → ℂ :=
  fun p => invSqrt2 * ∑ a : Bool, sgn (p.1 && a) * psi (a, p.2)

/-- The oracle `U_f : |x,y⟩ ↦ |x, y ⊕ f x⟩`, acting on amplitudes. -/
