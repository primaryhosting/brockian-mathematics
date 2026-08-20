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
# Is Betrothed Pair Iff Nontrivial Two Cycle
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.isBetrothedPair_iff_nontrivial_twoCycle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Brockian.BetrothedNumbers.Dynamics

open ArithmeticFunction

/-- The *quasi-aliquot* (betrothed partner) function:
`partner n = σ₁ n - n - 1`, i.e. the sum of the divisors of `n` other than `1` and `n`
(natural subtraction). -/

def IsNontrivialTwoCycle (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ partner m = n ∧ partner n = m

/-- **Betrothed pairs are exactly the nontrivial positive 2-cycles of
`partner n = σ₁ n - n - 1`.** -/
