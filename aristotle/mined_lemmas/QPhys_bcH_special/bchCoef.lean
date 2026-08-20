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

noncomputable def bchCoef (N j : ℕ) : ℚ :=
  if 2 * j ≤ N then (((N - 2 * j)! : ℚ) * (j ! : ℚ) * 2 ^ j)⁻¹ else 0

/-- The degree-`N` homogeneous component of `exp d * exp (2⁻¹ • c)`, where `c` is given
degree `2` and `d` degree `1`. -/
