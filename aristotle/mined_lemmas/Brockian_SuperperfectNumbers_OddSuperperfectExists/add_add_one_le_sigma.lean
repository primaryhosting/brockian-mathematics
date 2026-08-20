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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A natural number `n` is *superperfect* when `σ(σ(n)) = 2n`. Whether an odd superperfect
number exists is an open problem, so the target result
`Brockian.SuperperfectNumbers.OddSuperperfectExists` is a Lean-checked *conditional
reduction*: the existence of an odd superperfect number is equivalent to the existence of
one satisfying a list of proved necessary conditions (size lower bound from a kernel
computation, deficiency bounds, non-divisibility by `3` in the non-square case, and parity
information in the square case).
-/

namespace Brockian.SuperperfectNumbers

open Finset

/-- The sum-of-divisors function `σ(n) = ∑_{d ∣ n} d`. -/

lemma add_add_one_le_sigma {N a b : ℕ} (hN : N = a * b) (ha : 1 < a) (hb : 1 < b) :
    N + b + 1 ≤ sigma N := by
  have hNb : b < N := by
    subst hN; nlinarith
  have hsub : ({1, b} : Finset ℕ) ⊆ N.properDivisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Nat.mem_properDivisors.mpr ⟨one_dvd _, by omega⟩
    · exact Nat.mem_properDivisors.mpr ⟨⟨a, by rw [hN]; ring⟩, hNb⟩
  have hsum : ∑ d ∈ ({1, b} : Finset ℕ), d = 1 + b := by
    rw [Finset.sum_pair (by omega : (1 : ℕ) ≠ b)]
  have h2 : 1 + b ≤ ∑ d ∈ N.properDivisors, d :=
    hsum ▸ Finset.sum_le_sum_of_subset (f := fun d : ℕ => d) hsub
  rw [sigma_eq_properDivisors_add]
  omega

