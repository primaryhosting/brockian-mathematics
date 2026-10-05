import Mathlib

/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Betrothed (quasi-amicable) numbers are pairs `m ≠ n` of positive integers with
`s(m) = n + 1` and `s(n) = m + 1`, where `s` is the sum-of-proper-divisors function;
equivalently `σ(m) = σ(n) = m + n + 1`.  Pollack proved that the set of betrothed
numbers has asymptotic density zero.  This file does *not* claim that theorem.  It
delivers a **reduction**: the density-zero statement for betrothed numbers follows
from the density-zero statement for the (much simpler to describe, purely
`σ`-theoretic) set

`SmallerCandidates = {n | 2 * n + 2 ≤ σ(n) ∧ σ(σ(n) - n - 1) = σ(n)}`,

which contains exactly the *smaller* members of betrothed pairs.  The point of the
reduction is that one only ever has to treat the smaller member of a pair, and that
one may forget the pair structure entirely and work with the single arithmetic
condition above.

## Dependency graph

```
                       sigmaOne, Partner, Betrothed, partner        (definitions)
                                     |
              +----------------------+-----------------------+
              |                      |                       |
      Partner.symm            partner_eq_of_partner     Betrothed.pos
              |                      |
              +----------+-----------+
                         |
              Betrothed.partner_spec  --->  Betrothed.partner_ne
                         |                            |
              Betrothed.betrothed_partner             |
                         |                            |
              Betrothed.partner_partner  <------------+
                         |
     +-------------------+--------------------+
     |                                        |
 smallerSet_subset                 card_betrothed_le_two_mul   <--- (Finset injection)
     |                                        |
     +-------------------+--------------------+
                         |
      hasDensityZero_of_card_le (generic analytic lemma)
                         |
              density_zero_reduction          <-- TARGET
```

The two *reusable* analytic-number-theory lemmas isolated here are

* `Brockian.BetrothedNumbers.hasDensityZero_of_card_le` : if the counting function of a
  set is bounded by a constant multiple of the counting function of a density-zero set,
  the set has density zero;
* `Brockian.BetrothedNumbers.card_betrothed_le_two_mul` : the counting function of the
  betrothed numbers is at most twice the counting function of `SmallerCandidates`
  (an involution/injection argument, no analysis).

The remaining, genuinely analytic, input — density zero of `SmallerCandidates`, i.e. the
Erdős–Pollack estimate — is left as an explicit hypothesis and is *not* proved here.
-/

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

set_option grind.warning false

namespace Brockian.BetrothedNumbers

/-! ### Basic definitions -/

/-- The sum-of-divisors function `σ₁`. -/

def SmallerCandidates : Set ℕ :=
  {n | 2 * n + 2 ≤ sigmaOne n ∧ sigmaOne (sigmaOne n - n - 1) = sigmaOne n}

/-- `S` has asymptotic density zero. -/
