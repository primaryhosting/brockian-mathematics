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

theorem rep_of_le_1000 {n : ℕ} (h2 : 2 ≤ n) (hn : n ≤ 1000) : ErdosStrausRep n := by
  by_cases h1 : n % 24 = 1
  · have hcases : n = 25 ∨ n = 49 ∨ n = 73 ∨ n = 97 ∨ n = 121 ∨ n = 145 ∨ n = 169 ∨ n = 193 ∨ n = 217 ∨ n = 241 ∨ n = 265 ∨ n = 289 ∨ n = 313 ∨ n = 337 ∨ n = 361 ∨ n = 385 ∨ n = 409 ∨ n = 433 ∨ n = 457 ∨ n = 481 ∨ n = 505 ∨ n = 529 ∨ n = 553 ∨ n = 577 ∨ n = 601 ∨ n = 625 ∨ n = 649 ∨ n = 673 ∨ n = 697 ∨ n = 721 ∨ n = 745 ∨ n = 769 ∨ n = 793 ∨ n = 817 ∨ n = 841 ∨ n = 865 ∨ n = 889 ∨ n = 913 ∨ n = 937 ∨ n = 961 ∨ n = 985 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 5) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 7) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_73
    · exact rep_97
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 11) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 5) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 13) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_193
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 7) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_241
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 5) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 17) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_313
    · exact rep_337
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 19) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 5) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_409
    · exact rep_433
    · exact rep_457
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 13) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 5) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 23) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 7) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_577
    · exact rep_601
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 5) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 11) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_673
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 17) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 7) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 5) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_769
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 13) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 19) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 29) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 5) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 7) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 11) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_937
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 31) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 5) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
  · exact rep_of_mod_twentyFour_ne_one h2 h1

end Brockian.ErdosStraus

