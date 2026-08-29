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
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CarmichaelKorselt

/-- A Carmichael number: a composite `n > 1` such that Fermat's little theorem
congruence `a ^ (n - 1) ≡ 1 [MOD n]` holds for every `a` coprime to `n`. -/

lemma primeFactors_card_three {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) : (p * q * r).primeFactors.card = 3 := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hq0 : q ≠ 0 := hq.ne_zero
  have hr0 : r ≠ 0 := hr.ne_zero
  rw [Nat.primeFactors_mul (by positivity) hr0, Nat.primeFactors_mul hp0 hq0,
    hp.primeFactors, hq.primeFactors, hr.primeFactors]
  rw [Finset.card_eq_three]
  exact ⟨p, q, r, by omega, by omega, by omega, by simp⟩

/-- Chernick's construction: if `6k+1`, `12k+1`, `18k+1` are all prime and `k ≥ 1`,
then their product is a Carmichael number with exactly three prime factors. -/
