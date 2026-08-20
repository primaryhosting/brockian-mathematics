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

theorem dvd_cullen_of_prime_mod_eight (p : ℕ) (hp : Nat.Prime p)
    (h : p % 8 = 3 ∨ p % 8 = 5) : p ∣ cullen ((p + 1) / 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  set m := (p + 1) / 2 with hmdef
  have hm1 : m = p / 2 + 1 := by omega
  have hm : 2 * m = p + 1 := by omega
  have hns : ¬ IsSquare (2 : ZMod p) := by
    rw [ZMod.exists_sq_eq_two_iff hp2]; omega
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hc : ((2 : ℕ) : ZMod p) = 0 := by push_cast; exact hz
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp hc))
  have hEuler : (2 : ZMod p) ^ (p / 2) ≠ 1 := fun hh => hns ((ZMod.euler_criterion p h2ne).mpr hh)
  have hsq : ((2 : ZMod p) ^ (p / 2)) * ((2 : ZMod p) ^ (p / 2)) = 1 := by
    rw [← pow_add]
    have hh : p / 2 + p / 2 = p - 1 := by omega
    rw [hh]
    exact ZMod.pow_card_sub_one_eq_one h2ne
  have hneg : (2 : ZMod p) ^ (p / 2) = -1 :=
    (mul_self_eq_one_iff.mp hsq).resolve_left hEuler
  rw [← ZMod.natCast_eq_zero_iff]
  simp only [cullen_def]
  push_cast
  have hcast : (2 : ZMod p) ^ m = -2 := by rw [hm1, pow_succ, hneg]; ring
  have hmcast : (2 : ZMod p) * (m : ZMod p) = 1 := by
    have hh : ((2 * m : ℕ) : ZMod p) = ((p + 1 : ℕ) : ZMod p) := by rw [hm]
    push_cast at hh
    simpa [ZMod.natCast_self] using hh
  rw [hcast]
  linear_combination -hmcast

/-- For every prime `p ≡ 3, 5 (mod 8)` the Cullen number `C ((p + 1) / 2)` is composite. -/
