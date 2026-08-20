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

lemma no_two_roots {r M c x y : ℕ} (hr : Nat.Prime r) (hr2 : r ≠ 2) (hM : ¬ r ∣ M)
    (hxy : x < y) (hy : y ≤ 2) (h1 : r ∣ M * x + c) (h2 : r ∣ M * y + c) : False := by
  have hd : r ∣ (M * y + c) - (M * x + c) := Nat.dvd_sub h2 h1
  have hr3 : 3 ≤ r := by have := hr.two_le; omega
  have hM2 : ¬ r ∣ 2 * M := by
    intro h
    rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
    · exact hM h
  interval_cases y <;> interval_cases x
  · exact hM (by rwa [show M * 1 + c - (M * 0 + c) = M by omega] at hd)
  · exact hM2 (by rwa [show M * 2 + c - (M * 0 + c) = 2 * M by omega] at hd)
  · exact hM (by rwa [show M * 2 + c - (M * 1 + c) = M by omega] at hd)

/-- Admissibility of the pair of forms produced by the sieving construction. -/
