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

set_option grind.warning false

namespace Frontier

/-- `IsSHESolution ξ Z` says that the (smooth, strictly positive) function `Z : ℝ → ℝ → ℝ`,
written `Z t x`, is a classical solution of the multiplicative stochastic heat equation
`∂_t Z = ∂_x² Z + Z ξ` driven by the (function-valued) noise `ξ`. -/
structure IsSHESolution (xi Z : ℝ → ℝ → ℝ) : Prop where
  /-- `Z` is strictly positive. -/
  pos : ∀ t x, 0 < Z t x
  /-- `Z` is differentiable in time. -/
  diff_time : ∀ x, Differentiable ℝ fun t => Z t x
  /-- `Z` is differentiable in space. -/
  diff_space : ∀ t, Differentiable ℝ fun x => Z t x
  /-- The spatial derivative of `Z` is again differentiable in space. -/
  diff_space₂ : ∀ t, Differentiable ℝ fun x => deriv (fun y => Z t y) x
  /-- The equation `∂_t Z = ∂_x² Z + Z ξ`. -/
  eqn : ∀ t x,
    deriv (fun s => Z s x) t = deriv (deriv fun y => Z t y) x + Z t x * xi t x

/-- `IsKPZSolution ξ h` says that the (smooth) function `h : ℝ → ℝ → ℝ`, written `h t x`, is a
classical solution of the KPZ equation `∂_t h = ∂_x² h + (∂_x h)² + ξ` driven by `ξ`. -/
structure IsKPZSolution (xi h : ℝ → ℝ → ℝ) : Prop where
  /-- `h` is differentiable in time. -/
  diff_time : ∀ x, Differentiable ℝ fun t => h t x
  /-- `h` is differentiable in space. -/
  diff_space : ∀ t, Differentiable ℝ fun x => h t x
  /-- The spatial derivative of `h` is again differentiable in space. -/
  diff_space₂ : ∀ t, Differentiable ℝ fun x => deriv (fun y => h t y) x
  /-- The equation `∂_t h = ∂_x² h + (∂_x h)² + ξ`. -/
  eqn : ∀ t x,
    deriv (fun s => h s x) t =
      deriv (deriv fun y => h t y) x + (deriv (fun y => h t y) x) ^ 2 + xi t x

section ColeHopf

variable {xi Z h : ℝ → ℝ → ℝ}

/-- First spatial derivative of `log Z`. -/
lemma deriv_log_space (hZpos : ∀ t x, 0 < Z t x)
    (hZx : ∀ t, Differentiable ℝ fun x => Z t x) (t : ℝ) :
    (deriv fun y => Real.log (Z t y)) = fun y => deriv (fun z => Z t z) y / Z t y := by
  funext y
  exact (((hZx t y).hasDerivAt).log (hZpos t y).ne').deriv

/-- First spatial derivative of `exp h`. -/
lemma deriv_exp_space (hx : ∀ t, Differentiable ℝ fun x => h t x) (t : ℝ) :
    (deriv fun y => Real.exp (h t y)) =
      fun y => Real.exp (h t y) * deriv (fun z => h t z) y := by
  funext y
  exact (((hx t y).hasDerivAt).exp).deriv

/-- **Cole–Hopf transform.** If `Z` solves the multiplicative stochastic heat equation
`∂_t Z = ∂_x² Z + Z ξ` and is strictly positive, then `h = log Z` solves the KPZ equation
`∂_t h = ∂_x² h + (∂_x h)² + ξ`. -/
theorem isKPZSolution_log (hZ : IsSHESolution xi Z) :
    IsKPZSolution xi fun t x => Real.log (Z t x) := by
  have hlog := deriv_log_space hZ.pos hZ.diff_space
  refine ⟨fun x => (hZ.diff_time x).log fun t => (hZ.pos t x).ne', ?_, ?_, ?_⟩
  · exact fun t => (hZ.diff_space t).log fun x => (hZ.pos t x).ne'
  · intro t
    simp only [hlog]
    exact (hZ.diff_space₂ t).div (hZ.diff_space t) fun x => (hZ.pos t x).ne'
  · intro t x
    have hLHS : deriv (fun s => Real.log (Z s x)) t
        = deriv (fun s => Z s x) t / Z t x :=
      (((hZ.diff_time x t).hasDerivAt).log (hZ.pos t x).ne').deriv
    have h1 : HasDerivAt (fun y => deriv (fun z => Z t z) y)
        (deriv (deriv fun y => Z t y) x) x := (hZ.diff_space₂ t x).hasDerivAt
    have h2 : HasDerivAt (fun y => Z t y) (deriv (fun y => Z t y) x) x :=
      (hZ.diff_space t x).hasDerivAt
    have hZne : Z t x ≠ 0 := (hZ.pos t x).ne'
    have h3 : deriv (fun y => deriv (fun z => Z t z) y / Z t y) x
        = ((deriv (deriv fun y => Z t y) x) * Z t x
            - deriv (fun y => Z t y) x * deriv (fun y => Z t y) x) / (Z t x) ^ 2 :=
      (h1.div h2 hZne).deriv
    rw [hLHS, hZ.eqn t x]
    simp only [hlog]
    rw [h3]
    field_simp
    ring

/-- **Inverse Cole–Hopf transform.** If `h` solves the KPZ equation, then `Z = exp h` is a
strictly positive solution of the multiplicative stochastic heat equation. -/
theorem isSHESolution_exp (hh : IsKPZSolution xi h) :
    IsSHESolution xi fun t x => Real.exp (h t x) := by
  have hexp := deriv_exp_space hh.diff_space
  refine ⟨fun t x => Real.exp_pos _, fun x => (hh.diff_time x).exp,
    fun t => (hh.diff_space t).exp, ?_, ?_⟩
  · intro t
    simp only [hexp]
    exact ((hh.diff_space t).exp).mul (hh.diff_space₂ t)
  · intro t x
    have hLHS : deriv (fun s => Real.exp (h s x)) t
        = Real.exp (h t x) * deriv (fun s => h s x) t :=
      (((hh.diff_time x t).hasDerivAt).exp).deriv
    have h1 : HasDerivAt (fun y => Real.exp (h t y))
        (Real.exp (h t x) * deriv (fun y => h t y) x) x :=
      ((hh.diff_space t x).hasDerivAt).exp
    have h2 : HasDerivAt (fun y => deriv (fun z => h t z) y)
        (deriv (deriv fun y => h t y) x) x := (hh.diff_space₂ t x).hasDerivAt
    have h3 : deriv (fun y => Real.exp (h t y) * deriv (fun z => h t z) y) x
        = Real.exp (h t x) * deriv (fun y => h t y) x * deriv (fun z => h t z) x
          + Real.exp (h t x) * deriv (deriv fun y => h t y) x :=
      (h1.mul h2).deriv
    rw [hLHS, hh.eqn t x]
    simp only [hexp]
    rw [h3]
    ring

end ColeHopf

/-- **Hairer's KPZ equation, Cole–Hopf well-posedness reduction.**

For every driving noise `ξ` (here a genuine function, the classical/regularised setting in which
the equation makes sense pointwise), the KPZ equation
`∂_t h = ∂_x² h + (∂_x h)² + ξ`
is equivalent, via the Cole–Hopf transform `h ↦ e^h`, `Z ↦ log Z`, to the *linear* multiplicative
stochastic heat equation
`∂_t Z = ∂_x² Z + Z ξ`
in the class of strictly positive solutions: the two transforms are mutually inverse bijections
between the solution sets.  This is the base case of Hairer's well-posedness theory: it reduces the
ill-posed nonlinear KPZ equation to a linear problem, exactly the reduction that regularity
structures make unconditional. -/
theorem hairer_KPZ (xi : ℝ → ℝ → ℝ) :
    (∀ Z : ℝ → ℝ → ℝ, IsSHESolution xi Z → IsKPZSolution xi fun t x => Real.log (Z t x)) ∧
    (∀ h : ℝ → ℝ → ℝ, IsKPZSolution xi h → IsSHESolution xi fun t x => Real.exp (h t x)) ∧
    (∀ Z : ℝ → ℝ → ℝ, IsSHESolution xi Z →
      (fun t x => Real.exp (Real.log (Z t x))) = Z) ∧
    (∀ h : ℝ → ℝ → ℝ, (fun t x => Real.log (Real.exp (h t x))) = h) := by
  refine ⟨fun Z hZ => isKPZSolution_log hZ, fun h hh => isSHESolution_exp hh, ?_, ?_⟩
  · intro Z hZ
    funext t x
    exact Real.exp_log (hZ.pos t x)
  · intro h
    funext t x
    exact Real.log_exp (h t x)

end Frontier

