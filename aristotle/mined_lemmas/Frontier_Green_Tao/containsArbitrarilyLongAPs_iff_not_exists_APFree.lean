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

theorem containsArbitrarilyLongAPs_iff_not_exists_APFree (S : Set ℕ) :
    ContainsArbitrarilyLongAPs S ↔ ¬ ∃ k : ℕ, ¬ HasAPOfLength S k := by
  constructor
  · rintro h ⟨k, hk⟩
    exact hk (h k)
  · intro h k
    by_contra hk
    exact h ⟨k, hk⟩

/-- Equivalent "unbounded lengths" reformulation: it suffices to find, for each `k`, an AP of
length *at least* `k`. -/
