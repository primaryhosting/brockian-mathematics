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

/-!
# Cosine trace-norm bounds for Hermitian matrices (`CosTraceNorm` family)

For a Hermitian matrix `A` over an `RCLike` field `𝕜` we study the quantity
`cosTrace A = re (trace (cos A))`, where `cos A` is defined by the continuous functional
calculus, and compare it with the trace norm `traceNorm A = re (trace |A|)`
(the sum of the absolute values of the eigenvalues) and with `re (trace (A * A))`
(the squared Frobenius norm).
-/

namespace Brockian

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace of `cos A`, where `cos A` is defined via the continuous functional calculus. -/

noncomputable def traceNorm (A : Matrix n n 𝕜) : ℝ :=
  RCLike.re (Matrix.trace (cfc (fun x : ℝ => |x|) A))

/-- The trace of `f A` (continuous functional calculus) is the sum of `f` over the
eigenvalues. -/
