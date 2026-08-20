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
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a module docstring because Lean 4 requires `import`
commands to precede every other command, including module docstrings.)

## Contents

* `PolignacProperty n` : there are infinitely many pairs of consecutive primes `(p, p+n)`.
* `DicksonTwoForms` : Dickson's conjecture for two linear forms with equal leading
  coefficients.
* `PolignacConjecture` : Dickson's conjecture implies Polignac's conjecture for every
  positive even gap. This is a Lean-checked conditional reduction of Polignac's
  conjecture (which is open) to a standard prime-tuple hypothesis.
* `not_polignacProperty_of_odd` : unconditionally, Polignac's property fails for odd gaps.
* `polignacProperty_two_iff_twinPrimes` : for gap `2` Polignac's property is exactly the
  twin prime conjecture.
-/

namespace Brockian.PolignacPrimes

/-- `p` and `q` are consecutive primes: both are prime, `p < q`, and no prime lies
strictly between them. -/

lemma admissible {n M a : ℕ} (hn : Even n) (hM : Odd M)
    (hcop : ∀ r : ℕ, Nat.Prime r → r ∣ M → ¬ r ∣ a ∧ ¬ r ∣ (a + n)) :
    ∀ q : ℕ, Nat.Prime q → ∃ x : ℕ, ¬ (q ∣ (M * x + a) * (M * x + (a + n))) := by
  intro q hq
  by_cases hqM : q ∣ M
  · obtain ⟨h1, h2⟩ := hcop q hq hqM
    refine ⟨0, fun h => ?_⟩
    rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · exact h1 (by simpa using h)
    · exact h2 (by simpa using h)
  · by_cases hq2 : q = 2
    · subst hq2
      obtain ⟨m, hm⟩ := hn
      obtain ⟨k, hk⟩ := hM
      rcases Nat.even_or_odd a with ha | ha
      · obtain ⟨b, hb⟩ := ha
        refine ⟨1, fun h => ?_⟩
        rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h | h
        · obtain ⟨c, hc⟩ := h; omega
        · obtain ⟨c, hc⟩ := h; omega
      · obtain ⟨b, hb⟩ := ha
        refine ⟨0, fun h => ?_⟩
        rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h | h
        · obtain ⟨c, hc⟩ := h; omega
        · obtain ⟨c, hc⟩ := h; omega
    · by_contra hcon
      push_neg at hcon
      have h0 := (Nat.Prime.dvd_mul hq).mp (hcon 0)
      have h1 := (Nat.Prime.dvd_mul hq).mp (hcon 1)
      have h2 := (Nat.Prime.dvd_mul hq).mp (hcon 2)
      rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
        first
          | exact no_two_roots hq hq2 hqM (by omega) (by omega) h0 h1
          | exact no_two_roots hq hq2 hqM (by omega) (by omega) h0 h2
          | exact no_two_roots hq hq2 hqM (by omega) (by omega) h1 h2

/-- **Polignac's conjecture**, conditionally on Dickson's conjecture for two linear
forms: for every positive even `n` there are infinitely many pairs of consecutive
primes differing by `n`. -/
