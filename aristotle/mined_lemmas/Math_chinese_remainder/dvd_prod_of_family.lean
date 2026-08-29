/-!
# Chinese Remainder
Category: Pure Mathematics
Target: Math.chinese_remainder
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Function -- for the scoped `on` notation

namespace Math

/-- Each modulus of a finite family divides the product of the family. -/

theorem dvd_prod_of_family {ι : Type*} [Fintype ι] (n : ι → ℕ) (i : ι) :
    n i ∣ ∏ j, n j :=
  Finset.dvd_prod_of_mem n (Finset.mem_univ i)

/-- Any ring homomorphism out of `ZMod N` into `ZMod m`, where `m ∣ N`, is the canonical
reduction map. (`ZMod N` is a quotient of the initial ring `ℤ`, so such a map is unique.) -/
