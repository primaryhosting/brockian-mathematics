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

theorem containsArbitrarilyLongAPs_iff_forall_exists_ge (S : Set ℕ) :
    ContainsArbitrarilyLongAPs S ↔ ∀ k : ℕ, ∃ l, k ≤ l ∧ HasAPOfLength S l := by
  constructor
  · intro h k
    exact ⟨k, le_rfl, h k⟩
  · intro h k
    obtain ⟨l, hkl, hl⟩ := h k
    exact hl.mono hkl

/-! ## Unconditional base cases -/

/-- The ten-term arithmetic progression `199 + 210 i` (`i < 10`) consists of primes:
`199, 409, 619, 829, 1039, 1249, 1459, 1669, 1879, 2089`. -/
