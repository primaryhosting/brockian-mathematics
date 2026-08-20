import Mathlib
/-!
# Bc H Special
Category: Quantum Physics
Target: QPhys.bcH_special
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` to be the very first command in a file, so the header
comment appears immediately after it.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace QPhys

open Finset

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The degree-`N` homogeneous component of the product `exp a * exp b`. -/

lemma smul_left_cancel_rat {k : ℚ} (hk : k ≠ 0) {x y : A} (h : k • x = k • y) : x = y := by
  have h2 := congrArg (fun z : A => k⁻¹ • z) h
  simpa [smul_smul, inv_mul_cancel₀ hk] using h2

/-- The key graded identity: the homogeneous components of `exp a * exp b` and of
`exp (a+b) * exp (c/2)` agree. -/
