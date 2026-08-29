/-
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option grind.warning false

namespace Frontier

/-! ## Formalizing the statement -/

/-- `HasAPOfLength S k` says that the set `S ⊆ ℕ` contains an arithmetic progression
`a, a + d, …, a + (k-1) d` of length `k` with nonzero common difference `d`. -/

def ContainsArbitrarilyLongAPs (S : Set ℕ) : Prop :=
  ∀ k : ℕ, HasAPOfLength S k

/-- The Green–Tao theorem, as a proposition: the set of prime numbers contains
arithmetic progressions of every finite length. -/
