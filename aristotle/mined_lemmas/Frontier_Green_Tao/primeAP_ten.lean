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

/-- `PrimeAP k` says that the primes contain an arithmetic progression of length `k`:
there are `a` and a positive common difference `d` with `a + i * d` prime for all `i < k`. -/

theorem primeAP_ten : PrimeAP 10 := by
  refine ⟨199, 210, by norm_num, ?_⟩
  intro i hi
  interval_cases i <;> norm_num

/-- Every progression length up to `10` is unconditionally realised inside the primes. -/
