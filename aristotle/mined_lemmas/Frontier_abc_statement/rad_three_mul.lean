/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
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

/-- The radical of a natural number: the product of its distinct prime divisors. -/

lemma rad_three_mul {k : ℕ} (hk : k ≠ 0) (h3 : 3 ∣ k) : rad (3 * k) = rad k := by
  unfold rad
  have h3p : Nat.Prime 3 := by norm_num
  rw [Nat.primeFactors_mul (by norm_num) hk, h3p.primeFactors]
  congr 1
  rw [Finset.union_eq_right, Finset.singleton_subset_iff, Nat.mem_primeFactors]
  exact ⟨h3p, h3, hk⟩

