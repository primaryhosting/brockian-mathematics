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
def position (g : ℝ → ℂ) : ℝ → ℂ := fun x => (x : ℂ) * g x

/-- The momentum operator `p = -i ℏ d/dx` acting on complex-valued functions of one
real variable. -/
noncomputable def momentum (hbar : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => -Complex.I * hbar * deriv g x

/-- The commutator `[A, B] = A ∘ B - B ∘ A` of two operators on functions `ℝ → ℂ`. -/
def commutator (A B : (ℝ → ℂ) → (ℝ → ℂ)) (g : ℝ → ℂ) : ℝ → ℂ := A (B g) - B (A g)

/-- Leibniz rule for the position operator applied to a differentiable function:
`d/dx (x * g x) = g x + x * g' x`. -/
lemma deriv_position (g : ℝ → ℂ) (x : ℝ) (hg : DifferentiableAt ℝ g x) :
    deriv (position g) x = g x + (x : ℂ) * deriv g x := by
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x))
  have h := (h1.fun_mul hg.hasDerivAt).deriv
  rw [show position g = fun y : ℝ => (y : ℂ) * g y from rfl, h]
  ring

/-- The canonical commutation relation, pointwise, for any function differentiable at `x`. -/
theorem canonical_commutator_apply_of_differentiableAt (hbar : ℝ) (g : ℝ → ℂ) (x : ℝ)
    (hg : DifferentiableAt ℝ g x) :
    commutator position (momentum hbar) g x = Complex.I * hbar * g x := by
  simp only [commutator, position, momentum, Pi.sub_apply, deriv_position g x hg]
  ring

/-- **The canonical commutation relation.** On Schwartz space, with the position operator
`(X f)(x) = x f(x)` and the momentum operator `p = -i ℏ d/dx`, one has `[X, p] f = i ℏ f`. -/
theorem canonical_commutator (hbar : ℝ) (f : SchwartzMap ℝ ℂ) :
    commutator position (momentum hbar) (⇑f) = fun x => Complex.I * hbar * f x := by
  funext x
  exact canonical_commutator_apply_of_differentiableAt hbar (⇑f) x
    (SchwartzMap.differentiable f x)

/-- Pointwise form of the canonical commutation relation on Schwartz space. -/
theorem canonical_commutator_apply (hbar : ℝ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    (x : ℂ) * (-Complex.I * hbar * deriv (⇑f) x)
      - (-Complex.I * hbar * deriv (fun y : ℝ => (y : ℂ) * f y) x)
      = Complex.I * hbar * f x :=
  canonical_commutator_apply_of_differentiableAt hbar (⇑f) x (SchwartzMap.differentiable f x)

end QPhys

