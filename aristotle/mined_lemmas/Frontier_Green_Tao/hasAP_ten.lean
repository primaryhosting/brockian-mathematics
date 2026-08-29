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

theorem hasAP_ten : HasAPOfLength PrimeSet 10 := by
  refine ⟨199, 210, by norm_num, ?_⟩
  intro i hi
  interval_cases i <;> · simp only [PrimeSet, Set.mem_setOf_eq]; norm_num

/-- Unconditionally, the primes contain arithmetic progressions of every length `≤ 10`. -/
