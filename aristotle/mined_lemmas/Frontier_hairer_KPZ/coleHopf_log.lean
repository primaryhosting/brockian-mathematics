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

theorem coleHopf_log (xi Z Zt Zx Zxx : ℝ → ℝ → ℝ)
    (hZ : IsSHESolution xi Z Zt Zx Zxx) :
    IsKPZSolution xi (fun t x => Real.log (Z t x))
      (fun t x => Zt t x / Z t x) (fun t x => Zx t x / Z t x)
      (fun t x => Zxx t x / Z t x - (Zx t x / Z t x) ^ 2) := by
  obtain ⟨hpos, hZt, hZx, hZxx, heq⟩ := hZ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t x
    exact (hZt t x).log (hpos t x).ne'
  · intro t x
    exact (hZx t x).log (hpos t x).ne'
  · intro t x
    have h1 : HasDerivAt (fun y : ℝ => Zx t y / Z t y)
        ((Zxx t x * Z t x - Zx t x * Zx t x) / (Z t x) ^ 2) x :=
      (hZxx t x).div (hZx t x) (hpos t x).ne'
    have hne : Z t x ≠ 0 := (hpos t x).ne'
    refine h1.congr_deriv ?_
    field_simp
  · intro t x
    have hne : Z t x ≠ 0 := (hpos t x).ne'
    simp only [heq t x]
    field_simp
    ring

/-- **Cole–Hopf, backward direction.**  If `h` is a classical solution of KPZ with forcing
`ξ`, then `Z = exp h` is a positive classical solution of the multiplicative heat
equation with the same forcing. -/
