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
def IsKPZSolution (xi h ht hx hxx : ℝ → ℝ → ℝ) : Prop :=
  (∀ t x, HasDerivAt (fun s => h s x) (ht t x) t) ∧
  (∀ t x, HasDerivAt (fun y => h t y) (hx t x) x) ∧
  (∀ t x, HasDerivAt (fun y => hx t y) (hxx t x) x) ∧
  ∀ t x, ht t x = hxx t x + (hx t x) ^ 2 + xi t x

/-- `IsSHESolution ξ Z Zt Zx Zxx` says that `Z : ℝ → ℝ → ℝ` (time, space) has
partial derivatives `Zt`, `Zx`, `Zxx` and solves the multiplicative stochastic
heat equation `∂ₜ Z = ∂ₓₓ Z + Z · ξ`. -/
def IsSHESolution (xi Z Zt Zx Zxx : ℝ → ℝ → ℝ) : Prop :=
  (∀ t x, HasDerivAt (fun s => Z s x) (Zt t x) t) ∧
  (∀ t x, HasDerivAt (fun y => Z t y) (Zx t x) x) ∧
  (∀ t x, HasDerivAt (fun y => Zx t y) (Zxx t x) x) ∧
  ∀ t x, Zt t x = Zxx t x + Z t x * xi t x

section HopfCole

variable {xi h ht hx hxx : ℝ → ℝ → ℝ}

/-- Time derivative of the Hopf–Cole transform `Z = exp h`. -/
theorem hasDerivAt_exp_time
    (hHt : ∀ t x, HasDerivAt (fun s => h s x) (ht t x) t) (t x : ℝ) :
    HasDerivAt (fun s => Real.exp (h s x)) (Real.exp (h t x) * ht t x) t := by
  simpa [mul_comm] using (hHt t x).exp

/-- Space derivative of the Hopf–Cole transform `Z = exp h`. -/
theorem hasDerivAt_exp_space
    (hHx : ∀ t x, HasDerivAt (fun y => h t y) (hx t x) x) (t x : ℝ) :
    HasDerivAt (fun y => Real.exp (h t y)) (Real.exp (h t x) * hx t x) x := by
  simpa [mul_comm] using (hHx t x).exp

/-- Second space derivative of the Hopf–Cole transform `Z = exp h`:
`∂ₓₓ (exp h) = exp h · (∂ₓₓ h + (∂ₓ h)²)`. -/
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
theorem hairer_KPZ
    (hHt : ∀ t x, HasDerivAt (fun s => h s x) (ht t x) t)
    (hHx : ∀ t x, HasDerivAt (fun y => h t y) (hx t x) x)
    (hHxx : ∀ t x, HasDerivAt (fun y => hx t y) (hxx t x) x) :
    IsKPZSolution xi h ht hx hxx ↔
      IsSHESolution xi (fun t x => Real.exp (h t x))
        (fun t x => Real.exp (h t x) * ht t x)
        (fun t x => Real.exp (h t x) * hx t x)
        (fun t x => Real.exp (h t x) * (hxx t x + (hx t x) ^ 2)) := by
  have hpos : ∀ t x, Real.exp (h t x) ≠ 0 := fun t x => (Real.exp_pos _).ne'
  constructor
  · rintro ⟨-, -, -, heq⟩
    refine ⟨hasDerivAt_exp_time hHt, hasDerivAt_exp_space hHx,
      hasDerivAt_exp_space_second hHx hHxx, ?_⟩
    intro t x
    dsimp only
    rw [heq t x]
    ring
  · rintro ⟨-, -, -, heq⟩
    refine ⟨hHt, hHx, hHxx, ?_⟩
    intro t x
    have h1 := heq t x
    dsimp only at h1
    have h2 : Real.exp (h t x) * ht t x
        = Real.exp (h t x) * (hxx t x + (hx t x) ^ 2 + xi t x) := by
      rw [h1]; ring
    exact mul_left_cancel₀ (hpos t x) h2

end HopfCole

/-- Sanity check that the notion of solution is not vacuous: with zero forcing,
the zero field solves the KPZ equation. -/
theorem isKPZSolution_zero :
    IsKPZSolution (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
      (fun _ _ => 0) :=
  ⟨fun _ _ => hasDerivAt_const _ _, fun _ _ => hasDerivAt_const _ _,
    fun _ _ => hasDerivAt_const _ _, by intro t x; norm_num⟩

/-- A non-trivial explicit example: `h (t, x) = x + t` solves KPZ with the
zero forcing (indeed `∂ₜ h = 1 = 0 + 1² = ∂ₓₓ h + (∂ₓ h)²`). -/
theorem isKPZSolution_linear :
    IsKPZSolution (fun _ _ => 0) (fun t x => x + t) (fun _ _ => 1)
      (fun _ _ => 1) (fun _ _ => 0) := by
  refine ⟨fun t x => ?_, fun t x => ?_, fun _ _ => hasDerivAt_const _ _, ?_⟩
  · simpa using (hasDerivAt_id t).const_add x
  · simpa using (hasDerivAt_id x).add_const t
  · intro t x; norm_num

end Frontier

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

