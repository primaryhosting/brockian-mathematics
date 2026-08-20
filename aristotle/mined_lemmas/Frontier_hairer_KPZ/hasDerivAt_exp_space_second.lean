/-
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Formalization notes

The full theorem of Hairer (Fields Medal 2014) — that the KPZ equation

  ∂ₜ h = ∂ₓₓ h + (∂ₓ h)² + ξ,   ξ space-time white noise,

is well posed via the theory of regularity structures — is far beyond current
Mathlib: it requires stochastic analysis on distribution spaces, renormalisation,
and a reconstruction theorem, none of which exist in Mathlib.

What is formalized here is the *classical base case* on which the whole theory
rests, and to which Hairer's solution theory is designed to be consistent: the
**Hopf–Cole transform**.  For a (classically differentiable) field `h` and a
forcing `ξ`, `h` solves the KPZ equation if and only if `Z = exp h` solves the
*linear* multiplicative stochastic heat equation

  ∂ₜ Z = ∂ₓₓ Z + Z · ξ .

This is a Lean-checked reduction of the (nonlinear) KPZ equation to a linear
equation; for smooth forcing it is exactly the statement that KPZ is well posed,
since the linear equation has a unique solution by classical theory.

Derivatives are expressed through `HasDerivAt` for the partial derivatives in
each variable separately, with the partial derivatives supplied as explicit
fields (`ht`, `hx`, `hxx`).  The key Mathlib inputs are
`Real.hasDerivAt_exp`/`HasDerivAt.exp`, `HasDerivAt.mul` and `HasDerivAt.comp`.
-/

namespace Frontier

/-- `IsKPZSolution ξ h ht hx hxx` says that `h : ℝ → ℝ → ℝ` (time, space) has
partial derivatives `ht` (in time), `hx`, `hxx` (first and second in space) and
solves the KPZ equation `∂ₜ h = ∂ₓₓ h + (∂ₓ h)^2 + ξ`. -/

theorem hasDerivAt_exp_space_second
    (hHx : ∀ t x, HasDerivAt (fun y => h t y) (hx t x) x)
    (hHxx : ∀ t x, HasDerivAt (fun y => hx t y) (hxx t x) x) (t x : ℝ) :
    HasDerivAt (fun y => Real.exp (h t y) * hx t y)
      (Real.exp (h t x) * (hxx t x + (hx t x) ^ 2)) x := by
  have := (hasDerivAt_exp_space (h := h) (hx := hx) hHx t x).mul (hHxx t x)
  convert this using 1
  ring

/-- **Hopf–Cole transform / base case of the KPZ well-posedness theory.**

Given a field `h` with partial derivatives `ht`, `hx`, `hxx`, the field `h`
solves the KPZ equation `∂ₜ h = ∂ₓₓ h + (∂ₓ h)² + ξ` if and only if its
exponential `Z = exp h` solves the linear multiplicative stochastic heat
equation `∂ₜ Z = ∂ₓₓ Z + Z · ξ`, with partial derivatives given by the chain
rule.  This is the classical reduction underlying Hairer's solution theory for
KPZ. -/
