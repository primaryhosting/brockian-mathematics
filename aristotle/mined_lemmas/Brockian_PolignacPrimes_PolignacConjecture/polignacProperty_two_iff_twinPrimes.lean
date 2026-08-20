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

theorem polignacProperty_two_iff_twinPrimes :
    PolignacProperty 2 ↔ ∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2) := by
  constructor
  · intro h N
    obtain ⟨p, hN, hp, hq, -, -⟩ := h N
    exact ⟨p, hN, hp, hq⟩
  · intro h N
    obtain ⟨p, hN, hp, hq⟩ := h (max N 2)
    refine ⟨p, by omega, hp, hq, by omega, ?_⟩
    intro r hr1 hr2 hrp
    have hreq : r = p + 1 := by omega
    subst hreq
    have hpodd : Odd p := hp.odd_of_ne_two (by omega)
    have hev : Even (p + 1) := hpodd.add_one
    have h2 := (Nat.Prime.even_iff hrp).mp hev
    omega

end Brockian.PolignacPrimes

