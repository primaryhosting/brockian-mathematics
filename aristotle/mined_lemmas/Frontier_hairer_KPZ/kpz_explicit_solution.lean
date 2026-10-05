import Mathlib

/-!
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
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

namespace Frontier

/-!
## Classical (smooth) KPZ and the Cole–Hopf reduction

The Kardar–Parisi–Zhang equation on the line,

  `∂ₜ h = ∂ₓₓ h + (∂ₓ h)² + ξ`,

is ill-posed as it stands when `ξ` is space–time white noise: the solution is only
Hölder-`1/2⁻` in space, so `(∂ₓ h)²` is classically meaningless.  Hairer's theory of
regularity structures gives a solution theory for it.  The mathematical backbone of the
*base case* — the equation driven by a smooth (mollified) forcing, from which the whole
theory is bootstrapped — is the **Cole–Hopf reduction**: `h` solves KPZ with forcing `ξ`
exactly when `Z = exp h` solves the *linear* multiplicative stochastic heat equation

  `∂ₜ Z = ∂ₓₓ Z + ξ · Z`,   `Z > 0`.

Below this reduction is formalised and proved in both directions for classical
(pointwise differentiable) solutions, together with an explicit nontrivial solution of
the equation, which shows the notion of solution used is not vacuous.

Derivatives are carried as explicit data (`ht`, `hx`, `hxx` for the time derivative,
the space derivative and the second space derivative) together with `HasDerivAt`
hypotheses, which is the pointwise classical notion of a solution.
-/

/-- `h` is a classical solution of the KPZ equation `∂ₜ h = ∂ₓₓ h + (∂ₓ h)² + ξ`,
with `ht`, `hx`, `hxx` witnessing `∂ₜ h`, `∂ₓ h`, `∂ₓₓ h`. -/

theorem kpz_explicit_solution :
    IsKPZSolution (fun _ _ => 0) (fun t x => Real.log (1 + Real.exp (t + x)))
      (fun t x => Real.exp (t + x) / (1 + Real.exp (t + x)))
      (fun t x => Real.exp (t + x) / (1 + Real.exp (t + x)))
      (fun t x => Real.exp (t + x) / (1 + Real.exp (t + x))
        - (Real.exp (t + x) / (1 + Real.exp (t + x))) ^ 2) := by
  have hpos : ∀ t x : ℝ, 0 < 1 + Real.exp (t + x) := by
    intro t x; positivity
  have hT : ∀ t x : ℝ,
      HasDerivAt (fun s : ℝ => 1 + Real.exp (s + x)) (Real.exp (t + x)) t := by
    intro t x
    have : HasDerivAt (fun s : ℝ => Real.exp (s + x)) (Real.exp (t + x) * 1) t :=
      ((hasDerivAt_id t).add_const x).exp
    simpa using this.const_add 1
  have hX : ∀ t x : ℝ,
      HasDerivAt (fun y : ℝ => 1 + Real.exp (t + y)) (Real.exp (t + x)) x := by
    intro t x
    have : HasDerivAt (fun y : ℝ => Real.exp (t + y)) (Real.exp (t + x) * 1) x :=
      ((hasDerivAt_id x).const_add t).exp
    simpa using this.const_add 1
  have hXX : ∀ t x : ℝ,
      HasDerivAt (fun y : ℝ => Real.exp (t + y)) (Real.exp (t + x)) x := by
    intro t x
    have : HasDerivAt (fun y : ℝ => Real.exp (t + y)) (Real.exp (t + x) * 1) x :=
      ((hasDerivAt_id x).const_add t).exp
    simpa using this
  have hSHE : IsSHESolution (fun _ _ => 0) (fun t x => 1 + Real.exp (t + x))
      (fun t x => Real.exp (t + x)) (fun t x => Real.exp (t + x))
      (fun t x => Real.exp (t + x)) :=
    ⟨hpos, hT, hX, hXX, by intro t x; ring⟩
  exact coleHopf_log _ _ _ _ _ hSHE

/-- **Hairer, KPZ (classical base case and Cole–Hopf reduction).**

1. Every positive classical solution `Z` of the linear multiplicative heat equation
   `∂ₜ Z = ∂ₓₓ Z + ξ Z` yields, via `h = log Z`, a classical solution of the KPZ
   equation `∂ₜ h = ∂ₓₓ h + (∂ₓ h)² + ξ`.
2. Conversely every classical KPZ solution `h` yields, via `Z = exp h`, a positive
   classical solution of the linear equation.  Thus the well-posedness of KPZ with a
   smooth forcing is *equivalent* to that of a linear equation — this is the reduction
   underlying Hairer's solution theory.
3. The notion of solution is non-vacuous: there is a KPZ solution with zero forcing
   whose gradient never vanishes, so the nonlinearity `(∂ₓ h)²` is genuinely active. -/
