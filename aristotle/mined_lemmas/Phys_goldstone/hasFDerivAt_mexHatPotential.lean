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

theorem hasFDerivAt_mexHatPotential (p : ℝ × ℝ) :
    HasFDerivAt mexHatPotential (mexHatGrad p) p := by
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => q.1) (fst ℝ ℝ ℝ) p := (fst ℝ ℝ ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun q : ℝ × ℝ => q.2) (snd ℝ ℝ ℝ) p := (snd ℝ ℝ ℝ).hasFDerivAt
  have hq : HasFDerivAt (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2 - 1)
      ((2 * p.1) • (fst ℝ ℝ ℝ) + (2 * p.2) • (snd ℝ ℝ ℝ)) p := by
    simpa using ((h1.pow 2).add (h2.pow 2)).sub_const 1
  simpa [mexHatPotential, mexHatGrad] using hq.pow 2

