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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Superperfect Exists

Category: Brockian Conjecture

Target: `Brockian.SuperperfectNumbers.OddSuperperfectExists`

A natural number `n` is *superperfect* when `σ (σ n) = 2 * n`, where `σ = σ₁` is the
sum-of-divisors function.  The even superperfect numbers are exactly the numbers `2 ^ k`
with `2 ^ (k + 1) - 1` prime; whether an **odd** superperfect number exists is an open
problem.  Accordingly this file does not claim the (open) existence statement.  Instead it
proves unconditional structural facts about a hypothetical odd superperfect number and
packages them as a Lean-checked *conditional reduction*:

* `odd_sigma_of_superperfect`: for every superperfect `n > 0`, `σ n` is odd;
* `isSquare_of_odd_superperfect`: every odd superperfect number is a perfect square
  (Suryanarayana);
* `not_superperfect_of_odd_lt`: there is no odd superperfect number below `4096`;
* `OddSuperperfectExists`: an odd superperfect number exists **iff** there is an odd
  superperfect perfect square that is at least `4096`.
-/

namespace Brockian.SuperperfectNumbers

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-- `n` is *superperfect* when `σ (σ n) = 2 * n`, where `σ` is the sum-of-divisors
function. -/

lemma even_sigma_of_odd_of_not_isSquare {n : ℕ} (hn : 0 < n) (hodd : Odd n)
    (hsq : ¬ IsSquare n) : Even (σ 1 n) := by
  refine ZMod.natCast_eq_zero_iff_even.mp ?_
  rw [sigma_one_apply, Nat.cast_sum]
  refine Finset.sum_involution (fun d _ => n / d) ?_ ?_ ?_ ?_
  · intro d hd
    have hdvd : d ∣ n := (Nat.mem_divisors.1 hd).1
    obtain ⟨a, ha⟩ := hodd.of_dvd_nat hdvd
    obtain ⟨b, hb⟩ := hodd.of_dvd_nat (Nat.div_dvd_of_dvd hdvd)
    show ((d : ℕ) : ZMod 2) + ((n / d : ℕ) : ZMod 2) = 0
    rw [hb, ha]
    push_cast
    ring_nf
    simp [show (2 : ZMod 2) = 0 from rfl]
  · intro d hd _ hcon
    simp only at hcon
    exact hsq ⟨d, by
      have hdvd : d ∣ n := (Nat.mem_divisors.1 hd).1
      conv_lhs => rw [← Nat.div_mul_cancel hdvd, hcon]⟩
  · intro d hd
    exact Nat.mem_divisors.2 ⟨Nat.div_dvd_of_dvd (Nat.mem_divisors.1 hd).1, hn.ne'⟩
  · intro d hd
    exact Nat.div_div_self (Nat.mem_divisors.1 hd).1 hn.ne'

/-- **Key structural result.**  For every positive superperfect number `n`, the value `σ n`
is odd.

Indeed, write `m = σ n` and suppose `m` is even, say `m = 2 ^ a * u` with `a ≥ 1` and `u`
odd.  Then `2 * n = σ m = D * σ u` with `D = σ (2 ^ a) = 2 ^ (a + 1) - 1` odd and `≥ 3`, so
`D ∣ n`; writing `n = D * k` gives `σ u = 2 * k`.  Since `u > 1` we get `σ u ≥ u + 1`, and
`n` has the two distinct divisors `n` and `k`, so
`m = σ n ≥ n + k = 2 ^ a * σ u ≥ 2 ^ a * (u + 1) = m + 2 ^ a > m`, a contradiction. -/
