/-
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a plain comment at the very top of the file, since Lean 4
does not allow a module docstring to precede the `import` commands.)
-/

open Filter

namespace Frontier

/-- The `n`-th prime number (`nthPrime 0 = 2`). -/

theorem liminf_primeGap_le_of_bounded_prime_pairs (B : ℕ)
    (h : ∀ N : ℕ, ∃ p q : ℕ, N ≤ p ∧ p.Prime ∧ q.Prime ∧ p < q ∧ q ≤ p + B) :
    liminf (fun n => (primeGap n : ℕ∞)) atTop ≤ (B : ℕ∞) :=
  liminf_le_of_frequently_le'
    (((frequently_gap_le_iff B).2 h).mono fun n hn => by exact_mod_cast hn)

end Frontier

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

