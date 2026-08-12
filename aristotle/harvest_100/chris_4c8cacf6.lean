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

namespace Frontier

/-- **Infinitesimal invariance.**  If the Lagrangian `L` is invariant along the
one-parameter family of variations `q ↦ q + s • η` (with the velocity varied
accordingly), then the first-order invariance condition
`∂L/∂q · η + ∂L/∂v · η' = 0` holds along the path `q`.

Here `A t` and `B t` are the partial derivatives `∂L/∂q` and `∂L/∂v` evaluated
at `(q t, q' t)`, packaged through the joint Fréchet derivative of
`(x, v) ↦ L t x v`. -/
theorem infinitesimal_invariance
    (L : ℝ → ℝ → ℝ → ℝ) (q η A B : ℝ → ℝ)
    (hL : ∀ t : ℝ, HasFDerivAt (fun p : ℝ × ℝ => L t p.1 p.2)
      (A t • (ContinuousLinearMap.fst ℝ ℝ ℝ) + B t • (ContinuousLinearMap.snd ℝ ℝ ℝ))
      (q t, deriv q t))
    (hsym : ∀ s t : ℝ, L t (q t + s * η t) (deriv q t + s * deriv η t)
      = L t (q t) (deriv q t)) :
    ∀ t : ℝ, A t * η t + B t * deriv η t = 0 := by
  intro t
  -- the curve `s ↦ (q t + s η t, q' t + s η' t)` through `(q t, q' t)`
  have hcurve : HasDerivAt (fun s : ℝ => (q t + s * η t, deriv q t + s * deriv η t))
      (η t, deriv η t) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => q t + s * η t) (η t) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (η t)).const_add (q t)
    have h2 : HasDerivAt (fun s : ℝ => deriv q t + s * deriv η t) (deriv η t) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (deriv η t)).const_add (deriv q t)
    exact h1.prodMk h2
  have hL' : HasFDerivAt (fun p : ℝ × ℝ => L t p.1 p.2)
      (A t • (ContinuousLinearMap.fst ℝ ℝ ℝ) + B t • (ContinuousLinearMap.snd ℝ ℝ ℝ))
      (q t + 0 * η t, deriv q t + 0 * deriv η t) := by simpa using hL t
  have hcomp := hL'.comp_hasDerivAt (0 : ℝ) hcurve
  have hconst : HasDerivAt (fun s : ℝ => L t (q t + s * η t) (deriv q t + s * deriv η t))
      0 (0 : ℝ) := by
    simpa [hsym] using (hasDerivAt_const (0 : ℝ) (L t (q t) (deriv q t)))
  have := hcomp.unique hconst
  simpa [Function.comp] using this

/-- **Noether's theorem, one-dimensional case.**

Let `L t x v` be a Lagrangian, `q` a path, and let `A t`, `B t` denote the partial
derivatives `∂L/∂q`, `∂L/∂v` of `L` along `q` (hypothesis `hL`, phrased via the joint
Fréchet derivative).  Assume:

* `hEL` : the Euler–Lagrange equation `d/dt (∂L/∂v) = ∂L/∂q` holds along `q`;
* `hsym` : the action is invariant under the smooth symmetry
  `q ↦ q + s • η` (the integrand `L` itself is invariant to all orders in `s`).

Then the Noether current `J t = (∂L/∂v) · η t` is conserved: it is constant in time. -/
theorem noether_conservation
    (L : ℝ → ℝ → ℝ → ℝ) (q η A B : ℝ → ℝ)
    (hη : Differentiable ℝ η)
    (hL : ∀ t : ℝ, HasFDerivAt (fun p : ℝ × ℝ => L t p.1 p.2)
      (A t • (ContinuousLinearMap.fst ℝ ℝ ℝ) + B t • (ContinuousLinearMap.snd ℝ ℝ ℝ))
      (q t, deriv q t))
    (hEL : ∀ t : ℝ, HasDerivAt B (A t) t)
    (hsym : ∀ s t : ℝ, L t (q t + s * η t) (deriv q t + s * deriv η t)
      = L t (q t) (deriv q t)) :
    ∃ C : ℝ, ∀ t : ℝ, B t * η t = C := by
  have hinv := infinitesimal_invariance L q η A B hL hsym
  have hJ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => B t * η t) 0 t := by
    intro t
    have h := (hEL t).mul ((hη t).hasDerivAt)
    simpa [hinv t, add_comm] using h
  refine ⟨B 0 * η 0, fun t => ?_⟩
  have hdiff : Differentiable ℝ (fun t : ℝ => B t * η t) := fun t => (hJ t).differentiableAt
  have : ∀ x y : ℝ, (fun t : ℝ => B t * η t) x = (fun t : ℝ => B t * η t) y :=
    is_const_of_deriv_eq_zero hdiff (fun x => (hJ x).deriv)
  exact this t 0

end Frontier

section Sanity

/-- Non-vacuity check: the free particle `L t x v = v ^ 2 / 2` with a uniform-motion
solution `q t = v₀ * t` and the translation symmetry `η = 1` satisfies all hypotheses of
`Frontier.noether_conservation`; the conserved current is the momentum `v₀`. -/
example (v₀ : ℝ) :
    ∃ C : ℝ, ∀ t : ℝ, (fun _ : ℝ => v₀) t * (fun _ : ℝ => (1 : ℝ)) t = C := by
  refine Frontier.noether_conservation (fun _ _ v => v ^ 2 / 2) (fun t => v₀ * t)
    (fun _ => (1 : ℝ)) (fun _ => 0) (fun _ => v₀) (differentiable_const 1) ?_ ?_ ?_
  · intro t
    have hq : deriv (fun t : ℝ => v₀ * t) t = v₀ := by
      simpa using ((hasDerivAt_id t).const_mul v₀).deriv
    have : HasFDerivAt (fun p : ℝ × ℝ => p.2 ^ 2 / 2)
        ((0 : ℝ) • (ContinuousLinearMap.fst ℝ ℝ ℝ) + v₀ • (ContinuousLinearMap.snd ℝ ℝ ℝ))
        (v₀ * t, v₀) := by
      have h := ((((hasDerivAt_id (v₀ : ℝ)).pow 2).div_const 2).hasFDerivAt).comp (v₀ * t, v₀)
        (hasFDerivAt_snd (𝕜 := ℝ) (p := (v₀ * t, v₀)))
      convert h using 1
      refine ContinuousLinearMap.ext fun p => ?_
      simp
      ring
    simpa [hq] using this
  · intro t; simpa using hasDerivAt_const t v₀
  · intro s t; simp

end Sanity

