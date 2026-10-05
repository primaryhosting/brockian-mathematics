import Mathlib

/-!
# Mobius Root Sum 9
Category: Pure Mathematics
Target: Math.mobius_root_sum_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- The set of exponents `i < 9` with `gcd i 9 = 1`. -/

lemma coprime_filter_nine :
    (Finset.range 9).filter (fun i => Nat.Coprime i 9) = ({1, 2, 4, 5, 7, 8} : Finset ℕ) := by
  decide

/-- The sum of the primitive `9`-th roots of unity, expressed as a sum of powers of a
fixed primitive root. -/
