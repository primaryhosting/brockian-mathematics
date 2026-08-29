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

theorem not_invariant_iff_generator_ne_zero {A : E →L[ℝ] E} {x₀ : E} :
    (∃ t : ℝ, exp (t • A) x₀ ≠ x₀) ↔ A x₀ ≠ 0 := by
  refine ⟨generator_ne_zero_of_not_invariant, fun hne => ?_⟩
  by_contra hcon
  push_neg at hcon
  refine hne ?_
  have key : ∀ s : ℝ, HasDerivAt (fun u : ℝ => exp (u • A) x₀) (exp (s • A) (A x₀)) s :=
    hasDerivAt_exp_smul_apply A x₀
  have hzero : HasDerivAt (fun u : ℝ => exp (u • A) x₀) 0 0 := by
    simpa [hcon] using hasDerivAt_const (0 : ℝ) x₀
  have h := (key 0).unique hzero
  simpa using h

end Flow

/-- **Goldstone's theorem, infinitesimal form.**

If the gradient `D` of the potential annihilates the symmetry direction `A x` at every
configuration `x` (the Noether identity for a continuous symmetry), and `x₀` is a vacuum
(local minimum) at which the symmetry is broken (`A x₀ ≠ 0`), then the mass matrix `B`
(the Hessian of `V` at `x₀`) has the nonzero vector `A x₀` in its kernel: a massless
mode. -/
