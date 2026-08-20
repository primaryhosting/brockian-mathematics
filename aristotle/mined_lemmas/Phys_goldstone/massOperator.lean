import Mathlib
/-!
# Goldstone
Category: Frontier Phys
Target: Phys.goldstone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` to be the first command in a file, so the required
header comment is placed immediately after the single `import Mathlib` line.)
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-- The mass-squared operator (Hessian of the potential) at a field configuration `φ₀`:
the second derivative `D²V(φ₀)`, viewed as a continuous linear map sending a fluctuation
direction to the corresponding linear functional. In the physics normalization the mass
matrix of small fluctuations around `φ₀` is exactly this operator. -/

noncomputable def massOperator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E → ℝ) (φ₀ : E) : E →L[ℝ] (E →L[ℝ] ℝ) :=
  fderiv ℝ (fun x => fderiv ℝ V x) φ₀

/-- A direction `δ` is a *massless mode* of the potential `V` at `φ₀` when it is a nonzero
vector annihilated by the mass-squared operator, i.e. a nonzero element of the kernel of the
Hessian: fluctuations along `δ` cost no quadratic energy. -/
