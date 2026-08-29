import Mathlib

/-!
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- `IsGoldbachK2 n` : `n` is a sum of `K = 2` primes. -/

theorem no_goldbachK2_counterexample_le_631 :
    ¬ ∃ n : ℕ, Even n ∧ 4 ≤ n ∧ n ≤ 631 ∧ ¬ IsGoldbachK2 n := by
  rintro ⟨n, hn, h4, h631, hbad⟩
  exact hbad (isGoldbachK2_of_even_le_631 n hn h4 h631)

end Brockian

