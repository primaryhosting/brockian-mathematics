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

noncomputable def bchL (a b : A) (N : ℕ) : A :=
  ∑ m ∈ range (N + 1), ((m ! : ℚ) * ((N - m)! : ℚ))⁻¹ • (a ^ m * b ^ (N - m))

/-- Rational coefficients appearing in `bchR`. -/
