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

import Mathlib
/-!
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
The infinitude of Cullen primes (i.e. primes of the form `C n = n * 2 ^ n + 1`) is an
open problem, so what is proved here is a *Lean-checked conditional reduction*
together with unconditional partial results:

* `prime_cullen_of_proth_witness` : a Proth-type primality criterion for Cullen numbers
  (sufficiency, proved from scratch via orders in `ZMod q`);
* `exists_proth_witness_of_prime_cullen` : the converse (necessity);
* `CullenPrimeInfinitude` : if for arbitrarily large `n` the Cullen number `C n` has a
  Proth witness, then infinitely many Cullen numbers are prime;
* `cullen_prime_infinitude_iff` : the reduction is in fact an equivalence;
* `dvd_cullen_of_prime_mod_eight`, `infinite_composite_cullen` : unconditionally,
  infinitely many Cullen numbers are composite.
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/

theorem not_prime_cullen_of_prime_mod_eight (p : ℕ) (hp : Nat.Prime p)
    (h : p % 8 = 3 ∨ p % 8 = 5) : ¬ Nat.Prime (cullen ((p + 1) / 2)) := by
  intro hpr
  have hdvd := dvd_cullen_of_prime_mod_eight p hp h
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  set m := (p + 1) / 2 with hmdef
  have hm2 : 2 ≤ m := by omega
  have h4 : 4 ≤ 2 ^ m := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  have hlt : p < cullen m := by
    have : m * 4 ≤ m * 2 ^ m := Nat.mul_le_mul_left m h4
    simp only [cullen_def]
    omega
  rcases hpr.eq_one_or_self_of_dvd p hdvd with h1 | h1
  · exact hp.one_lt.ne' h1
  · omega

/-- **Unconditionally, there are infinitely many composite Cullen numbers.**
Indeed by Dirichlet's theorem there are infinitely many primes `p ≡ 3 (mod 8)`, and each
of them divides `C ((p + 1) / 2)`. -/
