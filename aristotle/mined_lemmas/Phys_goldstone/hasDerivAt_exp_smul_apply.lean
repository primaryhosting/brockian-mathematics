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

theorem hasDerivAt_exp_smul_apply (A : E →L[ℝ] E) (x : E) (s : ℝ) :
    HasDerivAt (fun t : ℝ => exp (t • A) x) (exp (s • A) (A x)) s := by
  have h := (ContinuousLinearMap.apply ℝ E x).hasFDerivAt.comp_hasDerivAt s
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) A s)
  simpa using h

/-- If the generator annihilates a configuration, that configuration is a fixed point of
the whole symmetry group: the symmetry is *unbroken* at `x₀`. -/
