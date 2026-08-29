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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Overview

A *Ruth–Aaron pair* is a pair of consecutive positive integers `(n, n+1)` whose sums of prime
factors, counted with multiplicity, agree:  `sopfr n = sopfr (n+1)`.  The first examples are
`(5,6)`, `(8,9)`, `(15,16)`, `(77,78)`, `(125,126)` and the famous `(714,715)`.

Whether there are infinitely many Ruth–Aaron pairs is an open problem (Erdős conjectured that
there are).  Accordingly, this file develops the theory and proves a *conditional reduction*:
Ruth–Aaron infinitude follows from a hypothesis asserting only the primality of two explicit
numbers, with no reference to sums of prime factors of the resulting pair.

The reduction rests on the following exact identity.  Write `Δ c = sopfr (c+1) - sopfr c`, put

  `p = 1 + (c+1) * Δ c`,  `q = 1 + c * Δ c`,  `n = c * p`.

Then, purely algebraically, `n + 1 = (c+1) * q`, and since `sopfr` is completely additive,

  `sopfr n = sopfr c + p`,  `sopfr (n+1) = sopfr (c+1) + q = sopfr c + Δ c + q = sopfr c + p`,

so `(n, n+1)` is a Ruth–Aaron pair *whenever `p` and `q` are both prime*.  Thus the sum-of-prime-
factors condition disappears entirely, and only a two-fold primality condition remains.

For instance `c = 1` gives `Δ = 2`, `q = 3`, `p = 5`, `n = 5`, the pair `(5,6)`; and `c = 12`
gives `Δ = 6`, `q = 73`, `p = 79`, `n = 948 = 2^2·3·79` with `949 = 13·73`, both of
sum-of-prime-factors `86`.
-/

namespace Brockian.RuthAaronPairs

open scoped Nat

/-- `sopfr n` is the sum of the prime factors of `n`, counted with multiplicity
(with the convention `sopfr 0 = sopfr 1 = 0`). -/

theorem exists_ruthAaronPair_gt_of_prime_pair {c : ℕ} (hc : 0 < c)
    (hp : Nat.Prime (1 + (c + 1) * sopfrExcess c))
    (hq : Nat.Prime (1 + c * sopfrExcess c)) :
    ∃ n, IsRuthAaronPair n ∧ c ≤ n := by
  set d := sopfrExcess c with hdef
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, Nat.mul_zero] at hq
      exact absurd hq Nat.not_prime_one
    · exact h
  have hd : sopfr (c + 1) = sopfr c + d := by
    have : d = sopfr (c + 1) - sopfr c := hdef
    omega
  refine ⟨c * (1 + (c + 1) * d), isRuthAaronPair_mul_of_prime hc hd hp hq, ?_⟩
  calc c = c * 1 := (Nat.mul_one c).symm
    _ ≤ c * (1 + (c + 1) * d) := Nat.mul_le_mul_left c (by omega)

/-- **Ruth–Aaron Infinitude (conditional).**  Assuming Hypothesis (P) — a statement about the
primality of two explicit numbers, with no reference to sums of prime factors — there are
infinitely many Ruth–Aaron pairs.

Unconditional infinitude of Ruth–Aaron pairs is an open problem; this theorem is a
Lean-checked reduction of it to Hypothesis (P). -/
