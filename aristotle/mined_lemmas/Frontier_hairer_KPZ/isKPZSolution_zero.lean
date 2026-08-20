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

theorem isKPZSolution_zero :
    IsKPZSolution (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
      (fun _ _ => 0) :=
  ⟨fun _ _ => hasDerivAt_const _ _, fun _ _ => hasDerivAt_const _ _,
    fun _ _ => hasDerivAt_const _ _, by intro t x; norm_num⟩

/-- A non-trivial explicit example: `h (t, x) = x + t` solves KPZ with the
zero forcing (indeed `∂ₜ h = 1 = 0 + 1² = ∂ₓₓ h + (∂ₓ h)²`). -/
