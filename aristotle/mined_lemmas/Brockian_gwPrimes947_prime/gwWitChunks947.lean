/-
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires the `import` lines to precede every command, including module
-- docstrings, so the header above is repeated verbatim as a module docstring below.)

import Mathlib

/-!
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

`Brockian.GoldbachWheelK2_947` extends the `GoldbachWheelK2` family to the wheel
modulus `947`: every even number `n` with `4 ≤ n ≤ 2 * 947 = 1894` is a sum of two
primes (`K = 2` summands).

Mathlib contains no Goldbach-type theorem to appeal to (the Goldbach conjecture is
open), so the finite range covered by this wheel is verified by an explicit
certificate:

* `gwPrimes947` is the list of all primes below `1894`; each entry is checked with
  the `Nat.Prime` extension of `norm_num` in `gwPrimes947_prime`.
* `gwWit947 i` is the least prime `p` for which `(4 + 2 * i) - p` is prime; the
  data is stored in `gwWitChunks947`.
* `gwCert947` checks, by kernel evaluation (`decide`), that for every `i < 946`
  both `gwWit947 i` and `4 + 2 * i - gwWit947 i` occur in `gwPrimes947`.
-/

set_option maxHeartbeats 4000000
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option grind.warning false

namespace Brockian

/-- All prime numbers below `2 * 947 = 1894`. -/

def gwWitChunks947 : List (List Nat) :=
[
  [
   2, 3, 3, 3, 5, 3, 3, 5, 3, 3, 5, 3, 5, 7, 3, 3, 5, 7, 3, 5, 3, 3, 5, 3, 5, 7, 3, 5, 7, 3, 3,
   5, 7, 3, 5, 3, 3, 5, 7, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3, 5, 3, 3, 5, 3, 3, 5, 3, 5, 7, 13, 11,
   13, 19, 3, 5, 3, 5, 7, 3, 3, 5, 7, 11, 11, 3, 3, 5, 7, 3, 5, 7, 3, 5, 3, 5, 7, 3, 5, 7, 3, 3,
   5, 7, 11, 11, 3, 3, 5, 3, 3 ],
  [
   5, 7, 11, 11, 13, 3, 5, 7, 23, 11, 13, 3, 5, 3, 3, 5, 3, 5, 7, 3, 3, 5, 7, 11, 11, 3, 5, 7,
   3, 5, 7, 3, 5, 7, 3, 3, 5, 7, 3, 5, 3, 3, 5, 7, 11, 11, 3, 5, 7, 19, 11, 13, 31, 3, 5, 3, 3,
   5, 3, 5, 7, 13, 11, 13, 19, 3, 5, 7, 3, 5, 7, 29, 11, 3, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3, 5, 7,
   3, 5, 7, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3, 5 ],
  [
   3, 5, 7, 13, 3, 5, 7, 17, 11, 3, 3, 5, 7, 11, 11, 3, 3, 5, 7, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3,
   5, 3, 3, 5, 3, 5, 7, 13, 11, 13, 3, 5, 7, 31, 3, 5, 3, 5, 7, 13, 3, 5, 3, 5, 7, 3, 5, 7, 19,
   11, 13, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 3, 5, 7, 3, 5, 7, 47, 11, 3, 5, 7, 3, 5, 7, 3, 3,
   5, 7, 3, 5, 7, 17, 11, 3, 5, 7, 3, 5, 7, 3 ],
  [
   3, 5, 7, 3, 5, 7, 3, 5, 3, 3, 5, 7, 11, 11, 13, 3, 5, 7, 23, 11, 3, 3, 5, 3, 5, 7, 3, 5, 7,
   3, 3, 5, 7, 11, 11, 13, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3, 5, 7, 17, 11, 3, 5, 7, 19, 3, 5, 7,
   17, 11, 3, 5, 7, 19, 3, 5, 7, 3, 5, 7, 3, 5, 3, 5, 7, 13, 3, 5, 7, 3, 5, 3, 5, 7, 13, 3, 5,
   3, 5, 7, 13, 11, 13, 19, 3, 5, 7, 23, 11, 3, 5 ],
  [
   7, 19, 11, 13, 3, 3, 5, 7, 11, 11, 3, 3, 5, 3, 3, 5, 7, 11, 11, 3, 5, 7, 19, 11, 13, 31, 3,
   5, 3, 3, 5, 3, 5, 7, 13, 11, 13, 19, 3, 5, 3, 3, 5, 3, 5, 7, 13, 11, 13, 19, 17, 19, 31, 3,
   5, 3, 5, 7, 13, 3, 5, 7, 17, 11, 3, 5, 7, 19, 3, 5, 3, 5, 7, 3, 5, 7, 3, 5, 7, 43, 11, 13,
   31, 3, 5, 3, 5, 7, 3, 5, 7, 3, 5, 7, 73, 3, 5, 7, 3, 5 ],
  [
   7, 23, 11, 13, 3, 5, 3, 5, 7, 3, 3, 5, 7, 11, 11, 3, 3, 5, 7, 3, 5, 7, 17, 11, 3, 3, 5, 7,
   11, 11, 3, 3, 5, 7, 3, 5, 7, 17, 11, 13, 23, 17, 19, 3, 5, 3, 3, 5, 3, 5, 7, 3, 5, 7, 3, 5,
   7, 31, 3, 5, 7, 3, 5, 7, 3, 5, 7, 29, 11, 13, 41, 17, 19, 41, 23, 3, 3, 5, 7, 11, 11, 3, 5,
   7, 19, 3, 5, 7, 17, 11, 3, 5, 7, 3, 5, 7, 3, 5, 7, 31 ],
  [
   3, 5, 7, 17, 11, 13, 3, 5, 3, 5, 7, 3, 5, 7, 3, 3, 5, 7, 3, 5, 7, 17, 11, 13, 3, 5, 7, 29,
   11, 3, 5, 7, 19, 11, 13, 37, 17, 19, 3, 3, 5, 3, 5, 7, 3, 3, 5, 7, 3, 5, 3, 3, 5, 3, 5, 7,
   13, 11, 13, 3, 3, 5, 7, 3, 5, 7, 17, 11, 13, 23, 17, 19, 29, 23, 31, 47, 29, 31, 41, 41, 3,
   5, 7, 3, 5, 7, 3, 5, 7, 61, 3, 5, 7, 17, 11, 13, 23, 17, 19, 3 ],
  [
   5, 7, 41, 11, 3, 5, 7, 19, 11, 13, 43, 3, 5, 3, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3, 5, 3, 3, 5, 7,
   3, 5, 7, 17, 11, 13, 3, 5, 7, 29, 11, 3, 3, 5, 3, 3, 5, 3, 5, 7, 3, 5, 7, 19, 11, 13, 3, 5,
   7, 31, 11, 13, 3, 5, 7, 43, 3, 5, 7, 17, 11, 13, 3, 5, 7, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3, 5,
   3, 5, 7, 13, 3, 5, 3, 5, 7, 13, 11, 13, 19, 3, 5 ],
  [
   3, 5, 7, 3, 3, 5, 3, 5, 7, 3, 3, 5, 7, 3, 5, 7, 17, 11, 3, 5, 7, 19, 11, 13, 31, 17, 19, 31,
   3, 5, 7, 3, 5, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 23, 23, 31, 3, 5, 3, 3, 5, 7, 11, 11, 3,
   5, 7, 19, 11, 13, 3, 3, 5, 7, 11, 11, 3, 5, 7, 19, 3, 5, 7, 3, 5, 7, 3, 5, 7, 3, 5, 7, 47,
   11, 13, 41, 17, 19, 3, 5, 7, 3, 5, 3, 3, 5, 7, 11, 11, 13 ],
  [
   3, 5, 7, 23, 11, 3, 5, 7, 19, 11, 13, 3, 5, 7, 31, 3, 5, 7, 17, 11, 13, 23, 17, 3, 5, 7, 67,
   11, 13, 31, 3, 5, 7, 3, 5, 3, 3, 5, 3, 3, 5, 7, 11, 11, 3, 5 ]
]

/-- The witness prime recorded for the even number `4 + 2 * i`. -/
