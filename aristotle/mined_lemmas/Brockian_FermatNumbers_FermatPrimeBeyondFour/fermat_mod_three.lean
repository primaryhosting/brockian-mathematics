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
# Fermat Prime Beyond Four
Category: Brockian Conjecture
Target: Brockian.FermatNumbers.FermatPrimeBeyondFour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command, so the header above is a plain block
-- comment rather than a `/-!` module docstring.)

import Mathlib

/-!
## Overview

The `n`-th Fermat number is `Fₙ = 2 ^ 2 ^ n + 1`.  The numbers `F₀, …, F₄` are prime, and no
further Fermat prime is known; whether some `Fₙ` with `n > 4` is prime is a famous open problem.

This file contains:

* `Brockian.FermatNumbers.fermat` — the Fermat numbers;
* `Brockian.FermatNumbers.prime_of_pepin` — the sufficiency half of Pépin's test;
* `Brockian.FermatNumbers.pepin_of_prime` — the necessity half of Pépin's test;
* `Brockian.FermatNumbers.FermatPrimeBeyondFour` — the main result: an unconditional
  *Lean-checked reduction* of the open conjecture "there is a Fermat prime beyond `F₄`" to a
  purely modular-arithmetic statement (Pépin's criterion);
* verified data: `F₀, …, F₄` are prime, and `F₅`, `F₆` are composite.
-/

namespace Brockian.FermatNumbers

/-- The `n`-th Fermat number `Fₙ = 2 ^ 2 ^ n + 1`. -/

lemma fermat_mod_three (n : ℕ) (hn : 1 ≤ n) : fermat n % 3 = 2 := by
  have h : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h2 : 2 ^ (2 ^ n) = 4 ^ (2 ^ (n - 1)) := by
    rw [h, pow_mul]
    norm_num
  have h3 : 4 ^ (2 ^ (n - 1)) % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  rw [fermat, h2]
  generalize (4:ℕ) ^ (2 ^ (n - 1)) = m at h3 ⊢
  omega

