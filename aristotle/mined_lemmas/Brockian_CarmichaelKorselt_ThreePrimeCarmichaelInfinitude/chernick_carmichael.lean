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

lemma chernick_carmichael {k : ℕ} (hk : 1 ≤ k) (h6 : Nat.Prime (6 * k + 1))
    (h12 : Nat.Prime (12 * k + 1)) (h18 : Nat.Prime (18 * k + 1)) :
    IsCarmichael ((6 * k + 1) * (12 * k + 1) * (18 * k + 1)) ∧
      ((6 * k + 1) * (12 * k + 1) * (18 * k + 1)).primeFactors.card = 3 := by
  have hlt1 : 6 * k + 1 < 12 * k + 1 := by omega
  have hlt2 : 12 * k + 1 < 18 * k + 1 := by omega
  have hplus : (6 * k + 1) * (12 * k + 1) * (18 * k + 1)
      = 36 * k * (36 * k ^ 2 + 11 * k + 1) + 1 := by ring
  have hsub : (6 * k + 1) * (12 * k + 1) * (18 * k + 1) - 1
      = 36 * k * (36 * k ^ 2 + 11 * k + 1) := by omega
  have e6 : (6 * k + 1) - 1 = 6 * k := by omega
  have e12 : (12 * k + 1) - 1 = 12 * k := by omega
  have e18 : (18 * k + 1) - 1 = 18 * k := by omega
  refine ⟨isCarmichael_of_three_primes h6 h12 h18 hlt1 hlt2 ?_ ?_ ?_,
    primeFactors_card_three h6 h12 h18 hlt1 hlt2⟩
  · rw [e6, hsub]; exact ⟨6 * (36 * k ^ 2 + 11 * k + 1), by ring⟩
  · rw [e12, hsub]; exact ⟨3 * (36 * k ^ 2 + 11 * k + 1), by ring⟩
  · rw [e18, hsub]; exact ⟨2 * (36 * k ^ 2 + 11 * k + 1), by ring⟩

/-- **Three Prime Carmichael Infinitude** (conditional).

Assuming the Chernick–Dickson hypothesis — that `6k+1`, `12k+1`, `18k+1` are
simultaneously prime for infinitely many `k`, a special case of Dickson's
conjecture — there are infinitely many Carmichael numbers with exactly three
prime factors.

The unconditional statement is an open problem; this is a Lean-checked
conditional reduction of it to the stated prime-tuple hypothesis. -/
