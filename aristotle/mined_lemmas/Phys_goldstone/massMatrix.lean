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

namespace Phys

section Goldstone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The mass (Hessian) matrix of a potential `V` at a point `v`: the second Fréchet
derivative of `V`, viewed as a bilinear form `E → E → ℝ`. -/

noncomputable def massMatrix (V : E → ℝ) (v : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fun x => fderiv ℝ V x) v

/-- **Infinitesimal invariance.** If a one–parameter family of transformations `g t`
leaves the potential `V` invariant, and its generator at `t = 0` is the linear map `T`,
then the gradient of `V` at any point `x` annihilates the symmetry direction `T x`. -/
