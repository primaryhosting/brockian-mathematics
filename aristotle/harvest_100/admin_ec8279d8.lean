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

open Complex

/-- The position operator `x̂`, acting on a function `ℝ → ℂ` by pointwise multiplication
by the (complexified) coordinate. -/
noncomputable def posOp (f : ℝ → ℂ) : ℝ → ℂ := fun x => (x : ℂ) * f x

/-- The momentum operator `p̂ = -i ℏ d/dx`, acting on a function `ℝ → ℂ`. -/
noncomputable def momOp (hbar : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => -(Complex.I * hbar) * deriv f x

/-- Derivative of `x ↦ x * f x` for a Schwartz function `f`. -/
lemma deriv_posOp (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (posOp (f : ℝ → ℂ)) x = f x + (x : ℂ) * deriv (f : ℝ → ℂ) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using Complex.ofRealCLM.hasDerivAt (x := x)
  have h2 : HasDerivAt (f : ℝ → ℂ) (deriv (f : ℝ → ℂ) x) x :=
    (SchwartzMap.differentiable f x).hasDerivAt
  have := h1.mul h2
  simpa [posOp, mul_comm, add_comm] using this.deriv

/-- **Canonical commutation relation.** For every Schwartz function `f : 𝓢(ℝ, ℂ)`, with the
position operator `x̂ f = x · f` and the momentum operator `p̂ = -i ℏ d/dx`, one has
`[x̂, p̂] f = i ℏ f` pointwise. -/
theorem canonical_commutator (hbar : ℝ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    posOp (momOp hbar (f : ℝ → ℂ)) x - momOp hbar (posOp (f : ℝ → ℂ)) x
      = Complex.I * hbar * f x := by
  simp only [posOp, momOp, deriv_posOp f x]
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

