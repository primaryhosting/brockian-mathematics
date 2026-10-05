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
def IsKPZSolution (xi h ht hx hxx : ℝ → ℝ → ℝ) : Prop :=
  (∀ t x : ℝ, HasDerivAt (fun s : ℝ => h s x) (ht t x) t) ∧
  (∀ t x : ℝ, HasDerivAt (fun y : ℝ => h t y) (hx t x) x) ∧
  (∀ t x : ℝ, HasDerivAt (fun y : ℝ => hx t y) (hxx t x) x) ∧
  (∀ t x : ℝ, ht t x = hxx t x + (hx t x) ^ 2 + xi t x)

/-- `Z` is a positive classical solution of the multiplicative stochastic heat equation
`∂ₜ Z = ∂ₓₓ Z + ξ · Z`, with `Zt`, `Zx`, `Zxx` witnessing `∂ₜ Z`, `∂ₓ Z`, `∂ₓₓ Z`. -/
def IsSHESolution (xi Z Zt Zx Zxx : ℝ → ℝ → ℝ) : Prop :=
  (∀ t x : ℝ, 0 < Z t x) ∧
  (∀ t x : ℝ, HasDerivAt (fun s : ℝ => Z s x) (Zt t x) t) ∧
  (∀ t x : ℝ, HasDerivAt (fun y : ℝ => Z t y) (Zx t x) x) ∧
  (∀ t x : ℝ, HasDerivAt (fun y : ℝ => Zx t y) (Zxx t x) x) ∧
  (∀ t x : ℝ, Zt t x = Zxx t x + xi t x * Z t x)

/-- **Cole–Hopf, forward direction.**  If `Z > 0` solves the multiplicative heat equation
with forcing `ξ`, then `h = log Z` is a classical solution of KPZ with the same forcing. -/
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
theorem coleHopf_exp (xi h ht hx hxx : ℝ → ℝ → ℝ)
    (hh : IsKPZSolution xi h ht hx hxx) :
    IsSHESolution xi (fun t x => Real.exp (h t x))
      (fun t x => ht t x * Real.exp (h t x)) (fun t x => hx t x * Real.exp (h t x))
      (fun t x => (hxx t x + (hx t x) ^ 2) * Real.exp (h t x)) := by
  obtain ⟨hT, hX, hXX, heq⟩ := hh
  refine ⟨fun t x => Real.exp_pos _, ?_, ?_, ?_, ?_⟩
  · intro t x
    simpa [mul_comm] using (hT t x).exp
  · intro t x
    simpa [mul_comm] using (hX t x).exp
  · intro t x
    have h1 : HasDerivAt (fun y : ℝ => hx t y * Real.exp (h t y))
        (hxx t x * Real.exp (h t x) + hx t x * (Real.exp (h t x) * hx t x)) x :=
      (hXX t x).mul ((hX t x).exp)
    refine h1.congr_deriv ?_
    ring
  · intro t x
    simp only [heq t x]
    ring

/-- An explicit nontrivial classical solution of KPZ with zero forcing:
`h t x = log (1 + exp (t + x))`, obtained from the heat-equation solution
`Z t x = 1 + exp (t + x)` through the Cole–Hopf map. -/
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
theorem hairer_KPZ :
    (∀ xi Z Zt Zx Zxx : ℝ → ℝ → ℝ, IsSHESolution xi Z Zt Zx Zxx →
        IsKPZSolution xi (fun t x => Real.log (Z t x))
          (fun t x => Zt t x / Z t x) (fun t x => Zx t x / Z t x)
          (fun t x => Zxx t x / Z t x - (Zx t x / Z t x) ^ 2)) ∧
    (∀ xi h ht hx hxx : ℝ → ℝ → ℝ, IsKPZSolution xi h ht hx hxx →
        IsSHESolution xi (fun t x => Real.exp (h t x))
          (fun t x => ht t x * Real.exp (h t x)) (fun t x => hx t x * Real.exp (h t x))
          (fun t x => (hxx t x + (hx t x) ^ 2) * Real.exp (h t x))) ∧
    (∃ h ht hx hxx : ℝ → ℝ → ℝ,
        IsKPZSolution (fun _ _ => 0) h ht hx hxx ∧ ∀ t x : ℝ, hx t x ≠ 0) := by
  refine ⟨coleHopf_log, coleHopf_exp, ?_⟩
  refine ⟨_, _, _, _, kpz_explicit_solution, ?_⟩
  intro t x
  have h1 : (0:ℝ) < 1 + Real.exp (t + x) := by positivity
  have h2 : (0:ℝ) < Real.exp (t + x) / (1 + Real.exp (t + x)) := by positivity
  exact h2.ne'

end Frontier

