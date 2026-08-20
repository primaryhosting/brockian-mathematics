import Mathlib

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Brockian

/-- The new wheel modulus: the prime `1153`. -/
abbrev wheelModulus : ℕ := 1153


lemma wheelModulus_prime : Nat.Prime wheelModulus := by
  norm_num [wheelModulus]

instance : Fact (Nat.Prime 1153) := ⟨by norm_num⟩

/-- The `K = 2` Goldbach wheel at modulus `M`: the set of residues `r` modulo `M` that are
admissible as the residue of one summand in a representation `n = a + b`, i.e. both `r` and
`n - r` are units modulo `M` (as must be the case when `a` and `b` are primes not dividing
`M`). -/
