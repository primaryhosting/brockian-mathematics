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
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace CarmichaelKorselt

/-- A *Carmichael number*: a composite `n > 1` which is a Fermat pseudoprime to every base,
i.e. `n ∣ a ^ n - a` for all integers `a`. -/

theorem primeFactors_card_chernickNum {k : ℕ} (h : ChernickTriple k) :
    (chernickNum k).primeFactors.card = 3 := by
  obtain ⟨hp, hq, hr⟩ := h
  have hk : 0 < k := chernick_pos ⟨hp, hq, hr⟩
  have e : (chernickNum k).primeFactors = {6 * k + 1, 12 * k + 1, 18 * k + 1} := by
    unfold chernickNum
    rw [Nat.primeFactors_mul (by positivity) (by positivity),
      Nat.primeFactors_mul (by positivity) (by positivity),
      hp.primeFactors, hq.primeFactors, hr.primeFactors]
    ext x; simp
  rw [e, Finset.card_insert_of_notMem (by simp; omega),
    Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]

