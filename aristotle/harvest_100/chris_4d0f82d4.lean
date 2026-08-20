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

namespace QPhys

open Complex SchwartzMap

/-- The position operator `X`, acting on complex-valued functions of a real variable
by multiplication with the coordinate: `(X f)(x) = x * f(x)`. -/
noncomputable def posOp (f : ℝ → ℂ) : ℝ → ℂ := fun x => (x : ℂ) * f x

/-- The momentum operator `P = -i ℏ d/dx`, acting on complex-valued functions of a real
variable. -/
noncomputable def momOp (hbar : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => -(Complex.I * hbar) * deriv f x

/-- The derivative of `x ↦ x * f x` for a Schwartz function `f`. -/
theorem hasDerivAt_posOp (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasDerivAt (posOp (f : ℝ → ℂ)) (f x + (x : ℂ) * deriv (f : ℝ → ℂ) x) x := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (f : ℝ → ℂ) (deriv (f : ℝ → ℂ) x) x :=
    (f.differentiable x).hasDerivAt
  have := h1.mul h2
  simpa [posOp, one_mul] using this

theorem deriv_posOp (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    deriv (posOp (f : ℝ → ℂ)) x = f x + (x : ℂ) * deriv (f : ℝ → ℂ) x :=
  (hasDerivAt_posOp f x).deriv

/-- **Canonical commutation relation.** On Schwartz space, with the momentum operator
`P = -i ℏ d/dx` and the position operator `(X f)(x) = x f(x)`, one has
`[X, P] f = i ℏ f`. -/
theorem canonical_commutator (hbar : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (posOp (momOp hbar (f : ℝ → ℂ)) - momOp hbar (posOp (f : ℝ → ℂ))) x
      = Complex.I * hbar * f x := by
  have hd : deriv (posOp (f : ℝ → ℂ)) x = f x + (x : ℂ) * deriv (f : ℝ → ℂ) x :=
    deriv_posOp f x
  simp only [Pi.sub_apply, posOp, momOp, hd]
  ring

end QPhys

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

