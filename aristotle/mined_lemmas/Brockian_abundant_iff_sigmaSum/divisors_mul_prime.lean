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
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Status of the target

`Brockian.WeirdNumbers.OddWeirdExists` states that some odd weird number exists
(weird = abundant but not pseudoperfect, in Mathlib's `Nat.Weird`). Whether an odd
weird number exists is an open problem, so it is stated here as a `Prop`-valued
definition and *not* asserted. What is proved unconditionally in this file is:

* `isWeird_mul_prime` : if `n` is weird and `p` is a prime exceeding the sum of the
  divisors of `n`, then `n * p` is weird;
* `oddWeirdExists_iff_infinite` : `OddWeirdExists` holds iff there are infinitely many
  odd weird numbers (a conditional reduction obtained from `isWeird_mul_prime`);
* `weird_seventy` : `70` is weird, so weird numbers do exist;
* `not_weird_of_odd_lt_946` : no odd number below `946` is weird, hence
  `oddWeird_ge_946` : any witness for `OddWeirdExists` is at least `946`.

Mathlib supplies the basic vocabulary (`Nat.Abundant`, `Nat.Pseudoperfect`, `Nat.Weird`
and `Nat.abundant_iff_sum_divisors` in `Mathlib/NumberTheory/FactorisationProperties.lean`,
all of which are used below), but no lemma there closes or nearly closes the target:
`exact?`/`apply?` find nothing, and Mathlib proves no existence results about weird
numbers at all, so everything below is developed from scratch.
-/

open Finset

namespace Brockian
namespace WeirdNumbers

/-- The sum of all (positive) divisors of `n`. -/

lemma divisors_mul_prime {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    (n * p).divisors = n.divisors ∪ n.divisors.image (fun d => p * d) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  ext d
  simp only [Finset.mem_union, Finset.mem_image, Nat.mem_divisors]
  constructor
  · rintro ⟨hd, -⟩
    by_cases hpd : p ∣ d
    · obtain ⟨e, rfl⟩ := hpd
      right
      refine ⟨e, ⟨?_, hn⟩, rfl⟩
      have hpe : p * e ∣ p * n := by
        rw [mul_comm n p] at hd; exact hd
      exact (mul_dvd_mul_iff_left hp0).mp hpe
    · left
      refine ⟨?_, hn⟩
      have hcop : Nat.Coprime d p :=
        Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd)
      exact hcop.dvd_of_dvd_mul_right hd
  · rintro (⟨hd, -⟩ | ⟨e, ⟨he, -⟩, rfl⟩)
    · exact ⟨hd.mul_right p, by positivity⟩
    · refine ⟨?_, by positivity⟩
      rw [mul_comm n p]
      exact mul_dvd_mul_left p he

