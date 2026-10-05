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
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Nat
open ArithmeticFunction

namespace Brockian.HyperperfectNumbers

/-- `n` is `k`-hyperperfect when `n = 1 + k * (σ n - n - 1)`.  Written without truncated
subtraction this reads `k * σ n + 1 = (k + 1) * n + k`.  For `k = 1` this is exactly
the condition that `n` is a perfect number. -/

private lemma wit {k p a q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (ha : 1 ≤ a)
    (heq : k * ((∑ i ∈ Finset.range (a + 1), p ^ i) * (q + 1)) + 1 = (k + 1) * (p ^ a * q) + k) :
    ∃ n, Hyperperfect k n :=
  ⟨_, hyperperfect_of_witness ⟨hp, hq, hne, ha, heq⟩⟩

/-- `6` is `1`-hyperperfect, i.e. perfect. -/
