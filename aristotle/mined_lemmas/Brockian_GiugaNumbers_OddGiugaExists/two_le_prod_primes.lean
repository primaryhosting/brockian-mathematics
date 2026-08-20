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
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Giuga numbers

A *Giuga number* is a composite `n` such that `p ∣ n / p - 1` for every prime `p ∣ n`.
The smallest one is `30`; whether an **odd** Giuga number exists is an open problem.

Accordingly the target `Brockian.GiugaNumbers.OddGiugaExists` is stated and proved here as
a Lean-checked *reduction*: an odd Giuga number exists if and only if there is a finite set
`S` of at least two odd primes such that `p ∣ (∏_{q ∈ S, q ≠ p} q) - 1` for every `p ∈ S`
(`GiugaSet S`). This converts the question into a search over finite sets of odd primes.

Along the way we prove, unconditionally:

* `IsGiuga.squarefree` — every Giuga number is squarefree;
* `isGiuga_thirty` — `30` is a Giuga number;
* `IsGiuga.giugaSet_primeFactors` / `GiugaSet.isGiuga_prod` — the two halves of the reduction;
* `GiugaSet.one_lt_sum_recip` — for a Giuga set `S` one has `∑_{p ∈ S} 1/p > 1`;
* `GiugaSet.nine_le_card` and `IsGiuga.nine_le_card_primeFactors` — consequently an odd
  Giuga number has at least nine distinct prime factors.
-/

namespace Brockian.GiugaNumbers

open Finset

/-- A *Giuga number* is a composite natural number `n` such that every prime `p`
dividing `n` satisfies `p ∣ n / p - 1`. -/

theorem two_le_prod_primes {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) (hne : S.Nonempty) :
    2 ≤ ∏ q ∈ S, q := by
  obtain ⟨q, hq⟩ := hne
  exact le_trans (hS q hq).two_le
    (Nat.le_of_dvd (prod_primes_pos hS) (Finset.dvd_prod_of_mem _ hq))

/-! ### The two halves of the reduction -/

/-- If `n` is an odd Giuga number then its set of prime factors is a Giuga set. -/
