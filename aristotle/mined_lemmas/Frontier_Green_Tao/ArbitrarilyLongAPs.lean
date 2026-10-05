import Mathlib

/-!
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- `A` contains an arithmetic progression of length `k`: there are a starting point `a`
and a positive common difference `d` with `a, a + d, …, a + (k-1) d` all in `A`. -/

theorem ArbitrarilyLongAPs.infinite_starting_points {A : Set ℕ} (h : ArbitrarilyLongAPs A)
    (k : ℕ) : {a : ℕ | ∃ d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨a, d, hd, hNa, ha⟩ := HasAPOfLength.shift (j := N + 1) (k := k) (h (N + 1 + k))
  exact ⟨a, ⟨d, hd, ha⟩, by omega⟩

/-- Green–Tao in its "infinitely many" form: granting the Erdős–Turán statement, for every `k`
there are infinitely many `k`-term arithmetic progressions of primes. -/
