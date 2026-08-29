import Mathlib

/-!
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

open Finset

/-- `HasAPOfLength S k` says that the set `S` contains a `k`-term arithmetic progression
`a, a + d, …, a + (k-1) d` with positive common difference `d`. -/

theorem greenTao_of_unbounded
    (h : ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ HasAPOfLength PrimeSet k) : GreenTaoStatement := by
  intro N
  obtain ⟨k, hk, hAP⟩ := h N
  exact hAP.mono hk

/-! ### Unconditional base cases -/

/-- `199, 409, 619, 829, 1039, 1249, 1459, 1669, 1879, 2089` is a 10-term arithmetic
progression of primes (common difference `210`). -/
