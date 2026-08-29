/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace QI

/-- The `n`-bit state space, an `n`-dimensional vector space over `ZMod 2`. -/
abbrev Vec (n : ℕ) := Fin n → ZMod 2

/-- The `ZMod 2`-valued inner product `⟪y, x⟫ = ∑ i, y i * x i`. -/

lemma ip_Y {n : ℕ} (s t : Vec n) (i k : Fin n) :
    ip (fun j => (if j = i then (1 : ZMod 2) else 0) + s i * (if j = k then 1 else 0)) t
      = t i + s i * t k := by
  simp [ip, add_mul, Finset.sum_add_distrib]

/-- **Recovery from `O(n)` samples.**  For every nonzero shift `s` there are `n` vectors
`Y i`, all orthogonal to `s`, such that `s` is the *unique* nonzero vector orthogonal to
all of them.  Thus `n` outcomes of Simon's quantum subroutine suffice to pin down `s`. -/
