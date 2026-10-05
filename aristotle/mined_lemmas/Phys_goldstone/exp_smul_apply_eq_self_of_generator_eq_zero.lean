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

theorem exp_smul_apply_eq_self_of_generator_eq_zero {A : E →L[ℝ] E} {x₀ : E}
    (h : A x₀ = 0) (t : ℝ) : exp (t • A) x₀ = x₀ := by
  have key : ∀ s : ℝ, HasDerivAt (fun u : ℝ => exp (u • A) x₀) 0 s := by
    intro s
    simpa [h] using hasDerivAt_exp_smul_apply A x₀ s
  have hdiff : Differentiable ℝ (fun u : ℝ => exp (u • A) x₀) :=
    fun s => (key s).differentiableAt
  have h0 := is_const_of_deriv_eq_zero hdiff (fun s => (key s).deriv) t 0
  simpa using h0

/-- **Spontaneous symmetry breaking**: if the vacuum `x₀` is not invariant under the
symmetry group, then the generator does not annihilate it, i.e. `A x₀ ≠ 0` is a genuine
direction along the (broken) symmetry orbit. -/
