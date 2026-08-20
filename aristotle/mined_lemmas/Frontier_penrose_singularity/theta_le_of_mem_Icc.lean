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

theorem theta_le_of_mem_Icc {c : ℝ} (hc : Set.Icc 0 c ⊆ Set.Ico 0 L) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) c) : C.theta t ≤ C.theta 0 := by
  have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) c, HasDerivAt C.theta (C.dtheta x) x := fun x hx =>
    C.hasDerivAt x (hc hx)
  have hcont : ContinuousOn C.theta (Set.Icc 0 c) := fun x hx =>
    ((hderiv x hx).continuousAt).continuousWithinAt
  have hint : interior (Set.Icc (0 : ℝ) c) ⊆ Set.Icc 0 c := interior_subset
  have hdiff : DifferentiableOn ℝ C.theta (interior (Set.Icc (0 : ℝ) c)) := fun x hx =>
    ((hderiv x (hint hx)).differentiableAt).differentiableWithinAt
  have hanti : AntitoneOn C.theta (Set.Icc 0 c) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 c) hcont hdiff ?_
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) c := hint hx
    have hd : deriv C.theta x = C.dtheta x := (hderiv x hx').deriv
    have := C.raychaudhuri x (hc hx')
    nlinarith [sq_nonneg (C.theta x), hd]
  exact hanti ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1

end NullCongruence

/-- **Penrose singularity theorem (focusing core).**

If the future-directed null geodesic congruence orthogonal to a trapped surface
satisfies the Raychaudhuri inequality coming from the null energy condition
(`theta' ≤ -theta ^ 2 / 2`) on its affine parameter range `[0, L)`, then that range is
necessarily bounded by `-2 / theta 0`.  Equivalently: the congruence focuses to a
conjugate (focal) point within affine parameter `-2 / theta 0`, and so the geodesics
cannot be extended indefinitely — the spacetime is null geodesically incomplete. -/
