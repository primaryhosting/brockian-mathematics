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

def gwWit947 (i : Nat) : Nat :=
  (gwWitChunks947.getD (i / 100) []).getD (i % 100) 0

set_option maxRecDepth 40000 in
