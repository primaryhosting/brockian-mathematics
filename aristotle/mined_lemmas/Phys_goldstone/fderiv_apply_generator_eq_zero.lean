import Mathlib

/-!
# Goldstone
Category: Frontier Phys
Target: Phys.goldstone
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
set_option pp.letVarTypes true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

open NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Infinitesimal (Noether) form of a continuous symmetry.**
If `V` is differentiable and invariant under a one-parameter family of transformations
`Φ t` with `Φ 0 = id` whose velocity field at `t = 0` is `A`, then the gradient of `V`
annihilates the symmetry direction `A x` at every field configuration `x`. -/

theorem fderiv_apply_generator_eq_zero {V : E → ℝ} {A : E → E} {Φ : ℝ → E → E}
    (hV : ∀ x : E, DifferentiableAt ℝ V x)
    (h0 : ∀ x : E, Φ 0 x = x)
    (hflow : ∀ x : E, HasDerivAt (fun t : ℝ => Φ t x) (A x) 0)
    (hinv : ∀ (t : ℝ) (x : E), V (Φ t x) = V x) (x : E) :
    fderiv ℝ V x (A x) = 0 := by
  have hcomp : HasDerivAt (fun t : ℝ => V (Φ t x)) (fderiv ℝ V x (A x)) 0 := by
    have h1 : HasFDerivAt V (fderiv ℝ V (Φ 0 x)) (Φ 0 x) := (hV (Φ 0 x)).hasFDerivAt
    have h2 := h1.comp_hasDerivAt (0 : ℝ) (hflow x)
    rw [h0 x] at h2
    exact h2
  have hconst : HasDerivAt (fun t : ℝ => V (Φ t x)) 0 0 := by
    simpa [hinv] using (hasDerivAt_const (0 : ℝ) (V x))
  exact hcomp.unique hconst

/-- **The Hessian of an invariant potential annihilates the symmetry direction at a
stationary point.**  This is the core algebraic content of Goldstone's theorem. -/
