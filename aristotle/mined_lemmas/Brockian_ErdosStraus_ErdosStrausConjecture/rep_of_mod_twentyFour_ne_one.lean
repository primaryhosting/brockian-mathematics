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
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Erdős–Straus conjecture states that for every `n ≥ 2` the fraction `4 / n` is the sum of
three unit fractions.  It is an open problem, so what is proved here are unconditional partial
results together with a reduction of the full conjecture to a thin family of primes:

* `rep_of_dvd`                : a representation for a divisor of `n` gives one for `n`;
* `rep_of_mod_four_eq_three`  : `n ≡ 3 [MOD 4]` is representable;
* `rep_of_mod_three_eq_two`   : `n ≡ 2 [MOD 3]` is representable;
* `rep_of_mod_twentyFour_eq_thirteen` : `n ≡ 13 [MOD 24]` is representable;
* `rep_of_mod_twentyFour_ne_one` : every `n ≥ 2` with `n % 24 ≠ 1` is representable;
* `erdosStrausConjecture_iff_prime_one_mod_twentyFour` : the conjecture is equivalent to its
  restriction to the primes `p ≡ 1 [MOD 24]`;
* `rep_of_le_1000` : the conjecture holds for all `2 ≤ n ≤ 1000`.

No Mathlib lemma proves the conjecture itself; the search of Mathlib turned up no statement about
Egyptian fraction representations of `4 / n`.
-/

namespace Brockian.ErdosStraus

/-- `ErdosStrausRep n` says that `4 / n` can be written as a sum of three unit fractions
with positive natural number denominators (repetitions allowed). -/

theorem rep_of_mod_twentyFour_ne_one {n : ℕ} (h2 : 2 ≤ n) (h : n % 24 ≠ 1) : ErdosStrausRep n := by
  rcases Nat.even_or_odd n with he | ho
  · exact rep_of_dvd he.two_dvd (by omega) rep_two
  · by_cases h3 : 3 ∣ n
    · exact rep_of_dvd h3 (by omega) rep_three
    · have hodd : n % 2 = 1 := Nat.odd_iff.mp ho
      have h3' : n % 3 ≠ 0 := fun hh => h3 (Nat.dvd_of_mod_eq_zero hh)
      have hsplit : n % 4 = 3 ∨ n % 3 = 2 ∨ n % 24 = 13 := by omega
      rcases hsplit with h4 | h4 | h4
      · exact rep_of_mod_four_eq_three h4
      · exact rep_of_mod_three_eq_two h4
      · exact rep_of_mod_twentyFour_eq_thirteen h4

/-- The conjecture holds for every `n ≥ 2` with `n % 12 ≠ 1`. -/
