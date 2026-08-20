import Mathlib

/-!
# Penrose Singularity
Category: Frontier Physics
Target: Frontier.penrose_singularity
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
## Setting

Mathlib does not (yet) contain Lorentzian causal theory, so the Penrose singularity

theorem rho_le_tangent (rho drho ddrho : ℝ → ℝ)
    (hrho : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt rho (drho t) t)
    (hdrho : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt drho (ddrho t) t)
    (hnec : ∀ t ∈ Set.Ici (0 : ℝ), ddrho t ≤ 0) :
    ∀ t ∈ Set.Ici (0 : ℝ), rho t ≤ rho 0 + drho 0 * t := by
  -- First: `drho` is antitone on `[0, ∞)`.
  have hdrho_anti : AntitoneOn drho (Set.Ici (0 : ℝ)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun x hx => ((hdrho x hx).continuousAt).continuousWithinAt)
      (fun x hx => ((hdrho x (interior_subset hx)).differentiableAt).differentiableWithinAt) ?_
    intro x hx
    have hx' : x ∈ Set.Ici (0 : ℝ) := interior_subset hx
    rw [(hdrho x hx').deriv]
    exact hnec x hx'
  -- Then `g t = rho t - (rho 0 + drho 0 * t)` has nonpositive derivative, so is antitone.
  set g : ℝ → ℝ := fun t => rho t - (rho 0 + drho 0 * t) with hgdef
  have hgderiv : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt g (drho t - drho 0) t := by
    intro t ht
    have h1 : HasDerivAt rho (drho t) t := hrho t ht
    have h2 : HasDerivAt (fun x : ℝ => rho 0 + drho 0 * x) (drho 0) t := by
      simpa using ((hasDerivAt_id t).const_mul (drho 0)).const_add (rho 0)
    exact h1.sub h2
  have hg_anti : AntitoneOn g (Set.Ici (0 : ℝ)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun x hx => ((hgderiv x hx).continuousAt).continuousWithinAt)
      (fun x hx => ((hgderiv x (interior_subset hx)).differentiableAt).differentiableWithinAt) ?_
    intro x hx
    have hx' : x ∈ Set.Ici (0 : ℝ) := interior_subset hx
    rw [(hgderiv x hx').deriv, sub_nonpos]
    exact hdrho_anti (Set.self_mem_Ici) hx' hx'
  intro t ht
  have := hg_anti (Set.self_mem_Ici) ht ht
  simp only [hgdef, mul_zero, add_zero, sub_self] at this
  linarith

/-- **Penrose singularity theorem: incompleteness, focal-point form.**

A trapped null congruence (`rho' 0 < 0`, `rho 0 > 0`) obeying the null energy condition in
Jacobi form (`rho'' ≤ 0`) cannot remain regular for all affine parameters: the transverse
area radius vanishes (a focal point of the trapped surface forms) at some affine parameter
`t ≤ -rho 0 / rho' 0`. -/
