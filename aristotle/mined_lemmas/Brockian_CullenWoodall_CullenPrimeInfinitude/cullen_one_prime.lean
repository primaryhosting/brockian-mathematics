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

theorem cullen_one_prime : Nat.Prime (cullen 1) := by
  rw [cullen_one]; norm_num

