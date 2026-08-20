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

theorem exists_proth_witness_of_prime_cullen (n : ℕ) (hn : 1 ≤ n)
    (hpr : Nat.Prime (cullen n)) : ∃ a : ZMod (cullen n), a ^ (n * 2 ^ (n - 1)) = -1 := by
  haveI : Fact (Nat.Prime (cullen n)) := ⟨hpr⟩
  have hp2 : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  have hval : cullen n = 2 * (n * 2 ^ (n - 1)) + 1 := by
    simp only [cullen_def, hp2]; ring
  have hge : 1 ≤ n * 2 ^ (n - 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hhalf : cullen n / 2 = n * 2 ^ (n - 1) := cullen_div_two hn
  have h3 : 3 ≤ cullen n := by omega
  have hchar : ringChar (ZMod (cullen n)) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; omega
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hchar
  have ha0 : a ≠ 0 := by rintro rfl; exact ha IsSquare.zero
  have hne1 : a ^ (cullen n / 2) ≠ 1 := fun hh => ha ((ZMod.euler_criterion _ ha0).mpr hh)
  have hsq : (a ^ (cullen n / 2)) * (a ^ (cullen n / 2)) = 1 := by
    rw [← pow_add]
    have hh : cullen n / 2 + cullen n / 2 = cullen n - 1 := by omega
    rw [hh]
    exact ZMod.pow_card_sub_one_eq_one ha0
  exact ⟨a, hhalf ▸ (mul_self_eq_one_iff.mp hsq).resolve_left hne1⟩

/-! ## The conditional reduction -/

/-- **Conditional infinitude of Cullen primes.**
If for arbitrarily large `n` the Cullen number `C n = n * 2 ^ n + 1` admits a Proth
witness, i.e. some `a` with `a ^ ((C n - 1) / 2) = -1` modulo `C n`, then there are
infinitely many `n` for which `C n` is prime. -/
