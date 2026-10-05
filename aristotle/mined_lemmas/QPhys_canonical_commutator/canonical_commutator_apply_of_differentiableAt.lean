/-
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QPhys

/-- The position operator `x` acting on complex-valued functions of one real variable:
`(X g)(x) = x * g x`. -/

theorem canonical_commutator_apply_of_differentiableAt (hbar : ℝ) (g : ℝ → ℂ) (x : ℝ)
    (hg : DifferentiableAt ℝ g x) :
    commutator position (momentum hbar) g x = Complex.I * hbar * g x := by
  simp only [commutator, position, momentum, Pi.sub_apply, deriv_position g x hg]
  ring

/-- **The canonical commutation relation.** On Schwartz space, with the position operator
`(X f)(x) = x f(x)` and the momentum operator `p = -i ℏ d/dx`, one has `[X, p] f = i ℏ f`. -/
