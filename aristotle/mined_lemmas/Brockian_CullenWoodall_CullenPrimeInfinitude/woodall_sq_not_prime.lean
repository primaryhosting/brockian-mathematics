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
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
Note on the header: Lean 4 requires `import` to be the very first command of a file, so the
header above is a plain block comment (`/- ... -/`) rather than a module docstring (`/-! ... -/`);
its text is otherwise verbatim.

## Contents

* Cullen numbers `C n = n * 2 ^ n + 1` and Woodall numbers `W n = n * 2 ^ n - 1`.
* `CullenPrimeInfinitude` / `WoodallPrimeInfinitude`: Lean-checked *conditional reductions* of the
  (open) infinitude conjectures to the corresponding unboundedness hypotheses, together with
  `cullenPrimeConjecture_iff_unbounded` / `woodallPrimeConjecture_iff_unbounded`.
* Unconditional partial results: explicit arithmetic progressions of composite Cullen numbers
  (`p ∣ C (p - 2 + k * p * (p - 1))` for every odd prime `p`), the companion Woodall divisibility
  `p ∣ W ((p - 1) ^ 2)`, and the resulting infinitude of composite Cullen and Woodall numbers.

Nothing about Cullen or Woodall numbers is currently available in Mathlib; the arithmetic input
used here is Fermat's little theorem in the form `ZMod.pow_card_sub_one_eq_one`, together with
`Nat.exists_infinite_primes` and `Set.infinite_of_forall_exists_gt`.
-/

namespace Brockian.CullenWoodall

/-! ## Cullen numbers -/

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/

theorem woodall_sq_not_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ IsWoodallPrime ((p - 1) ^ 2) := by
  intro hprime
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  set n := (p - 1) ^ 2 with hn
  have hpn : p ≤ n := by
    have h1 : p - 1 + 1 = p := by omega
    have h2 : 2 ≤ p - 1 := by omega
    have : (p - 1) * 2 ≤ (p - 1) * (p - 1) := Nat.mul_le_mul_left _ h2
    have hsq : n = (p - 1) * (p - 1) := by rw [hn]; ring
    omega
  have hn2 : 2 ≤ n := by omega
  have hdvd : p ∣ woodall n := prime_dvd_woodall_sq hp hp2
  have hlt : p < woodall n := lt_of_le_of_lt hpn (lt_woodall hn2)
  rcases hprime.eq_one_or_self_of_dvd p hdvd with h | h
  · omega
  · omega

/-- Infinitely many Woodall numbers are composite. -/
