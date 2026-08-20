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

theorem gwCert947 :
    ∀ i ∈ Finset.range 946,
      gwWit947 i ∈ gwPrimes947 ∧
      4 + 2 * i - gwWit947 i ∈ gwPrimes947 ∧
      gwWit947 i ≤ 4 + 2 * i := by
  intro i hi
  simp only [Finset.mem_range] at hi
  rcases (by omega : i < 100 ∨ 100 ≤ i ∧ i < 200 ∨ 200 ≤ i ∧ i < 300 ∨ 300 ≤ i ∧ i < 400 ∨
      400 ≤ i ∧ i < 500 ∨ 500 ≤ i ∧ i < 600 ∨ 600 ≤ i ∧ i < 700 ∨ 700 ≤ i ∧ i < 800 ∨
      800 ≤ i ∧ i < 900 ∨ 900 ≤ i) with h | h | h | h | h | h | h | h | h | h
  · have h := gwCert947_block0 (i - 0) (by simp only [Finset.mem_range]; omega)
    rwa [show 0 + (i - 0) = i from by omega] at h
  · have h := gwCert947_block1 (i - 100) (by simp only [Finset.mem_range]; omega)
    rwa [show 100 + (i - 100) = i from by omega] at h
  · have h := gwCert947_block2 (i - 200) (by simp only [Finset.mem_range]; omega)
    rwa [show 200 + (i - 200) = i from by omega] at h
  · have h := gwCert947_block3 (i - 300) (by simp only [Finset.mem_range]; omega)
    rwa [show 300 + (i - 300) = i from by omega] at h
  · have h := gwCert947_block4 (i - 400) (by simp only [Finset.mem_range]; omega)
    rwa [show 400 + (i - 400) = i from by omega] at h
  · have h := gwCert947_block5 (i - 500) (by simp only [Finset.mem_range]; omega)
    rwa [show 500 + (i - 500) = i from by omega] at h
  · have h := gwCert947_block6 (i - 600) (by simp only [Finset.mem_range]; omega)
    rwa [show 600 + (i - 600) = i from by omega] at h
  · have h := gwCert947_block7 (i - 700) (by simp only [Finset.mem_range]; omega)
    rwa [show 700 + (i - 700) = i from by omega] at h
  · have h := gwCert947_block8 (i - 800) (by simp only [Finset.mem_range]; omega)
    rwa [show 800 + (i - 800) = i from by omega] at h
  · have h := gwCert947_block9 (i - 900) (by simp only [Finset.mem_range]; omega)
    rwa [show 900 + (i - 900) = i from by omega] at h

/-- **Goldbach wheel `K = 2`, modulus `947`.**

Every even number `n` with `4 ≤ n ≤ 2 * 947` is the sum of two primes. -/
