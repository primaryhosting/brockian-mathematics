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
import Brockian.BrocardProblem

/-!
# Brocard's problem, in Mathlib's vocabulary

`Brockian/BrocardProblem.lean` is import-free (so that the required header
comment can be its first line), and therefore defines factorial itself as
`Brockian.BrocardProblem.fact`.  Here we check that `fact` agrees with Mathlib's
`Nat.factorial` and restate the two main results using `Nat.factorial`.
-/

namespace Brockian.BrocardProblem

open Nat

/-- The self-contained factorial of `Brockian/BrocardProblem.lean` agrees with
Mathlib's `Nat.factorial`. -/

theorem brocard_factorial_conjecture
    (H : ∀ n : ℕ, 1000 < n → ∃ p : ℕ, 0 < p ∧ ∀ x < p, x * x % p ≠ (n ! + 1) % p)
    (n m : ℕ) (h : n ! + 1 = m ^ 2) : n = 4 ∨ n = 5 ∨ n = 7 := by
  refine BrocardConjecture (fun k hk => ?_) n m (by rw [fact_eq_factorial]; exact h)
  simpa [HasCertificate, fact_eq_factorial] using H k hk

end Brockian.BrocardProblem

/-!
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
## Brocard's problem

Brocard's problem asks for all solutions in natural numbers of

  `n ! + 1 = m ^ 2`.

The only known solutions are `n = 4, 5, 7` (with `m = 5, 11, 71`), and the
assertion that there are no others is *Brocard's conjecture*, an open problem.

This file is deliberately self-contained (it has no `import`s, so that the
required header comment can be the very first thing in the file: Lean does not
allow a module docstring to precede an `import`).  Factorial is therefore
defined here as `Brockian.BrocardProblem.fact`; the companion file
`Brockian/BrocardMathlib.lean` proves `fact n = Nat.factorial n` and restates
the results in Mathlib's vocabulary.

Contents:

* `ne_sq_of_mod_witness` — the certificate lemma: a natural number that is a
  quadratic non-residue modulo some `p > 0` is not a perfect square;
* `certificate_of_le_1000` — for every `8 ≤ n ≤ 1000` an explicit modulus `p`
  (a prime `> n`) is exhibited, together with the value `r = (n ! + 1) % p`,
  such that `n ! + 1` is a non-residue mod `p`; this is checked by the kernel;
* `brocard_verified_upTo_1000` — the unconditional partial result: the only
  solutions with `n ≤ 1000` are `n = 4, 5, 7`;
* `BrocardConjecture` — the conditional reduction: Brocard's conjecture follows
  from the existence of a modular non-residue certificate for every `n > 1000`.
-/

namespace Brockian.BrocardProblem

/-- Factorial, `fact n = n !`. -/
