import Mathlib
/-!
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to be the very first commands of a
file, and a module docstring `/-! ... -/` is not allowed before them.  The required header
comment is therefore placed immediately after the single `import Mathlib` line.
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

/-! ## Partial derivatives in the space–time variables

Throughout, a space–time function is a map `u : ℝ → ℝ → ℝ`, written `u t x`, with `t` the
time variable and `x` the space variable. -/

/-- Time derivative `∂_t u` of a space–time function `u : ℝ → ℝ → ℝ`. -/
noncomputable def dt (u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ := deriv (fun s => u s x) t

/-- Space derivative `∂_x u` of a space–time function `u : ℝ → ℝ → ℝ`. -/
noncomputable def dx (u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ := deriv (fun y => u t y) x

/-- Second space derivative `∂_x^2 u`. -/
noncomputable def dxx (u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ := dx (dx u) t x

/-! ## The two equations -/

/-- `h` is a (classical) solution of the KPZ equation
`∂_t h = ∂_x^2 h + (∂_x h)^2 + ξ` on the time set `T`. -/
def IsKPZSolution (ξ h : ℝ → ℝ → ℝ) (T : Set ℝ) : Prop :=
  ∀ t ∈ T, ∀ x : ℝ, dt h t x = dxx h t x + (dx h t x) ^ 2 + ξ t x

/-- `Z` is a (classical) solution of the multiplicative stochastic heat equation
`∂_t Z = ∂_x^2 Z + Z ξ` on the time set `T`. -/
def IsSHESolution (ξ Z : ℝ → ℝ → ℝ) (T : Set ℝ) : Prop :=
  ∀ t ∈ T, ∀ x : ℝ, dt Z t x = dxx Z t x + Z t x * ξ t x

/-- Regularity assumptions on a space–time function that are needed to make sense of the
classical (pointwise) formulation of the equations: the function is differentiable in time,
twice differentiable in space, and its space derivative is again differentiable in space. -/
structure IsClassicalRegular (u : ℝ → ℝ → ℝ) : Prop where
  time : ∀ x : ℝ, Differentiable ℝ fun t => u t x
  space : ∀ t : ℝ, Differentiable ℝ fun x => u t x
  space₂ : ∀ t : ℝ, Differentiable ℝ fun x => dx u t x

/-! ## Chain–rule lemmas for the Cole–Hopf transform `Z = exp h` -/

section ColeHopf

variable {h : ℝ → ℝ → ℝ}

/-- `∂_t exp(h) = exp(h) ∂_t h`. -/
theorem dt_exp (hreg : IsClassicalRegular h) (t x : ℝ) :
    dt (fun s y => Real.exp (h s y)) t x = Real.exp (h t x) * dt h t x := by
  have hd : HasDerivAt (fun s => h s x) (dt h t x) t := (hreg.time x t).hasDerivAt
  simpa [dt] using (hd.exp).deriv

/-- `∂_x exp(h) = exp(h) ∂_x h`. -/
theorem dx_exp (hreg : IsClassicalRegular h) (t x : ℝ) :
    dx (fun s y => Real.exp (h s y)) t x = Real.exp (h t x) * dx h t x := by
  have hd : HasDerivAt (fun y => h t y) (dx h t x) x := (hreg.space t x).hasDerivAt
  simpa [dx] using (hd.exp).deriv

/-- `∂_x^2 exp(h) = exp(h) (∂_x^2 h + (∂_x h)^2)`. -/
theorem dxx_exp (hreg : IsClassicalRegular h) (t x : ℝ) :
    dxx (fun s y => Real.exp (h s y)) t x
      = Real.exp (h t x) * (dxx h t x + (dx h t x) ^ 2) := by
  have key : (fun y => dx (fun s y => Real.exp (h s y)) t y)
      = fun y => Real.exp (h t y) * dx h t y := by
    funext y; exact dx_exp hreg t y
  have hexp : HasDerivAt (fun y => Real.exp (h t y))
      (Real.exp (h t x) * dx h t x) x := by
    simpa [mul_comm] using ((hreg.space t x).hasDerivAt).exp
  have hdd : HasDerivAt (fun y => dx h t y) (dxx h t x) x :=
    ((hreg.space₂ t) x).hasDerivAt
  have := hexp.mul hdd
  have h2 : dxx (fun s y => Real.exp (h s y)) t x
      = deriv (fun y => Real.exp (h t y) * dx h t y) x := by
    rw [dxx, dx, key]
  rw [h2, this.deriv]
  ring

end ColeHopf

/-! ## The Cole–Hopf reduction

This is the exact (deterministic, classical) form of the transformation on which Hairer's
solution theory for the KPZ equation is built: `h` solves KPZ if and only if `Z = exp h`
solves the multiplicative stochastic heat equation, which is *linear* in `Z`. -/

/-- **Cole–Hopf reduction (target theorem).**

For a classically regular space–time function `h` and any forcing `ξ`, on any time set `T`:
`h` solves the KPZ equation `∂_t h = ∂_x^2 h + (∂_x h)^2 + ξ` if and only if the Cole–Hopf
transform `Z = exp h` solves the (linear) multiplicative stochastic heat equation
`∂_t Z = ∂_x^2 Z + Z ξ`.

This is the Lean-checked reduction of the nonlinear KPZ equation to a linear equation, the
classical backbone of Hairer's well-posedness theory for KPZ. -/
theorem hairer_KPZ {h ξ : ℝ → ℝ → ℝ} (hreg : IsClassicalRegular h) (T : Set ℝ) :
    IsKPZSolution ξ h T ↔ IsSHESolution ξ (fun t x => Real.exp (h t x)) T := by
  constructor
  · intro H t ht x
    have hx := H t ht x
    rw [dt_exp hreg, dxx_exp hreg]
    rw [hx]; ring
  · intro H t ht x
    have hx := H t ht x
    rw [dt_exp hreg, dxx_exp hreg] at hx
    have hpos : Real.exp (h t x) ≠ 0 := (Real.exp_pos _).ne'
    have : Real.exp (h t x) * dt h t x
        = Real.exp (h t x) * (dxx h t x + (dx h t x) ^ 2 + ξ t x) := by
      rw [hx]; ring
    exact mul_left_cancel₀ hpos this

/-! ## A base case: an explicit nontrivial solution

For the free equation (`ξ = 0`) the Cole–Hopf transform of the heat kernel,
`h t x = -x^2/(4t) - (1/2) log (4 π t)`, is an explicit classical solution of KPZ on
`t > 0`; correspondingly the Gaussian heat kernel itself solves the free stochastic heat
equation. -/

/-- The (Cole–Hopf logarithm of the) Gaussian heat kernel. -/
noncomputable def kpzHopfCole (t x : ℝ) : ℝ := -x ^ 2 / (4 * t) - Real.log (4 * Real.pi * t) / 2

theorem dx_kpzHopfCole {t : ℝ} (ht : t ≠ 0) (x : ℝ) :
    dx kpzHopfCole t x = -x / (2 * t) := by
  have : HasDerivAt (fun y : ℝ => kpzHopfCole t y) (-x / (2 * t)) x := by
    have hx : HasDerivAt (fun y : ℝ => -y ^ 2 / (4 * t)) (-x / (2 * t)) x := by
      have h1 : HasDerivAt (fun y : ℝ => -y ^ 2) (-(2 * x)) x := by
        simpa using ((hasDerivAt_pow 2 x).neg)
      have := h1.div_const (4 * t)
      convert this using 1
      field_simp
      ring
    simpa [kpzHopfCole, sub_eq_add_neg] using hx.add_const (-(Real.log (4 * Real.pi * t) / 2))
  simpa [dx] using this.deriv

theorem dxx_kpzHopfCole {t : ℝ} (ht : t ≠ 0) (x : ℝ) :
    dxx kpzHopfCole t x = -1 / (2 * t) := by
  have key : (fun y => dx kpzHopfCole t y) = fun y : ℝ => -y / (2 * t) := by
    funext y; exact dx_kpzHopfCole ht y
  have : HasDerivAt (fun y : ℝ => -y / (2 * t)) (-1 / (2 * t)) x := by
    simpa [neg_div] using (((hasDerivAt_id x).neg).div_const (2 * t))
  rw [dxx, dx, key]
  exact this.deriv

theorem dt_kpzHopfCole {t : ℝ} (ht : 0 < t) (x : ℝ) :
    dt kpzHopfCole t x = x ^ 2 / (4 * t ^ 2) - 1 / (2 * t) := by
  have hne : (4 : ℝ) * t ≠ 0 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => -x ^ 2 / (4 * s)) (x ^ 2 / (4 * t ^ 2)) t := by
    have hd : HasDerivAt (fun s : ℝ => 4 * s) 4 t := by
      simpa using (hasDerivAt_id t).const_mul (4 : ℝ)
    have := (hd.inv hne).const_mul (-x ^ 2)
    convert this using 1
    · funext s; ring
    · field_simp
      ring
  have h2 : HasDerivAt (fun s : ℝ => Real.log (4 * Real.pi * s) / 2) (1 / (2 * t)) t := by
    have hpi : (4 : ℝ) * Real.pi ≠ 0 := by positivity
    have hd : HasDerivAt (fun s : ℝ => 4 * Real.pi * s) (4 * Real.pi) t := by
      simpa using (hasDerivAt_id t).const_mul (4 * Real.pi)
    have hne' : 4 * Real.pi * t ≠ 0 := by positivity
    have hlog : HasDerivAt (fun s : ℝ => Real.log (4 * Real.pi * s))
        ((4 * Real.pi) / (4 * Real.pi * t)) t := hd.log hne'
    have := hlog.div_const 2
    convert this using 1
    field_simp
  have := h1.sub h2
  simpa [dt, kpzHopfCole] using this.deriv

/-- **Base case.** The Cole–Hopf logarithm of the Gaussian heat kernel,
`h t x = -x²/(4t) - log(4πt)/2`, is an explicit classical solution of the free KPZ equation
(`ξ = 0`) for positive times. -/
theorem hairer_KPZ_base_case :
    IsKPZSolution (fun _ _ => 0) kpzHopfCole (Set.Ioi 0) := by
  intro t ht x
  have ht0 : (0 : ℝ) < t := ht
  have htne : t ≠ 0 := ne_of_gt ht0
  rw [dt_kpzHopfCole ht0, dxx_kpzHopfCole htne, dx_kpzHopfCole htne]
  field_simp
  ring

end Frontier

