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
# Sierpinski Problem
Category: Brockian Conjecture
Target: Brockian.SierpinskiCovering.SierpinskiProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not permit a `/-! ... -/` module docstring before `import`; the requested
-- header is reproduced verbatim as a module docstring immediately after the import below.)

import Mathlib

/-!
# Sierpinski Problem
Category: Brockian Conjecture
Target: Brockian.SierpinskiCovering.SierpinskiProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.SierpinskiCovering

/-!
## The Sierpiński problem

A *Sierpiński number* is an odd natural number `k` such that `k * 2 ^ n + 1` is composite
for every natural number `n`.  Sierpiński proved in 1960 that infinitely many such `k` exist;
Selfridge showed in 1962 that `k = 78557` is one of them, and it is conjectured to be the
smallest.

The proof for `78557` is by a *covering system*: the seven primes
`{3, 5, 7, 13, 19, 37, 73}` have multiplicative order of `2` dividing `36`
(orders `2, 4, 3, 12, 18, 36, 9` respectively), and for every residue `r < 36` at least one of
them divides `78557 * 2 ^ r + 1`.  Since `2 ^ 36 ≡ 1` modulo each of these primes, the same
prime then divides `78557 * 2 ^ n + 1` for every `n ≡ r [MOD 36]`.

Remark on Mathlib coverage: Mathlib does not contain the Sierpiński problem, Sierpiński
numbers, or covering systems, so the argument is developed from scratch here.  The only
external ingredients used are the elementary `Nat.ModEq` API (`Nat.ModEq.pow`,
`Nat.ModEq.mul_left`, `Nat.ModEq.add_right`, `Nat.modEq_zero_iff_dvd`) and
`Nat.Prime.eq_one_or_self_of_dvd`.
-/

/-- The covering table: for each residue `r < 36` the entry `covList[r]` is a prime from the
covering set `{3, 5, 7, 13, 19, 37, 73}` that divides `78557 * 2 ^ r + 1`. -/

lemma cov_dvd (n : ℕ) : cov (n % 36) ∣ 78557 * 2 ^ n + 1 := by
  set r := n % 36 with hrdef
  have hr : r < 36 := Nat.mod_lt _ (by norm_num)
  set p := cov r
  have hp2 : 2 ≤ p := (cov_bounds r hr).1
  -- `2 ^ 36 ≡ 1 [MOD p]`
  have h1 : (2 : ℕ) ^ 36 ≡ 1 [MOD p] := by
    have := cov_two_pow_36 r hr
    unfold Nat.ModEq
    rw [this, Nat.mod_eq_of_lt hp2]
  -- hence `2 ^ n ≡ 2 ^ r [MOD p]`
  have hn : n = 36 * (n / 36) + r := by rw [hrdef]; omega
  have h2 : (2 : ℕ) ^ n ≡ 2 ^ r [MOD p] := by
    conv_lhs => rw [hn]
    rw [pow_add, pow_mul]
    calc ((2 : ℕ) ^ 36) ^ (n / 36) * 2 ^ r
        ≡ 1 ^ (n / 36) * 2 ^ r [MOD p] := Nat.ModEq.mul_right _ (h1.pow _)
      _ = 2 ^ r := by rw [one_pow, one_mul]
  have h3 : 78557 * 2 ^ n + 1 ≡ 78557 * 2 ^ r + 1 [MOD p] :=
    (h2.mul_left 78557).add_right 1
  have h4 : 78557 * 2 ^ r + 1 ≡ 0 [MOD p] :=
    (Nat.modEq_zero_iff_dvd).mpr (cov_dvd_base r hr)
  exact (Nat.modEq_zero_iff_dvd).mp (h3.trans h4)

/-- **The Sierpiński problem (Selfridge's covering witness).**
`78557` is a Sierpiński number: `78557 * 2 ^ n + 1` is never prime. -/
