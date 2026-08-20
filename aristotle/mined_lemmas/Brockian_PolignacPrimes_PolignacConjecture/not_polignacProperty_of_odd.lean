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

theorem not_polignacProperty_of_odd {n : ℕ} (hn : Odd n) : ¬ PolignacProperty n := by
  intro h
  obtain ⟨p, hp2, hpp, hqq, hlt, -⟩ := h 2
  have hpodd : Odd p := hpp.odd_of_ne_two (by omega)
  have hev : Even (p + n) := hpodd.add_odd hn
  have h2 := (Nat.Prime.even_iff hqq).mp hev
  obtain ⟨m, hm⟩ := hn
  omega

/-- For the gap `2`, Polignac's property is equivalent to the twin prime conjecture. -/
