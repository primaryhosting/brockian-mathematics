import Mathlib

/-!
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
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

namespace Brockian
namespace BetrothedNumbers

open Finset
open scoped ArithmeticFunction.sigma

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: both are positive, they are distinct,
and the sum of the divisors of each, other than the number itself and `1`, gives the other;
equivalently `σ m = σ n = m + n + 1`. -/

lemma sigma_three_mul_ge {r : ℕ} (hr : 4 ≤ r) : 4 * r + 4 ≤ σ 1 (3 * r) := by
  have hq : 3 * r ≠ 0 := by omega
  have hsub : ({1, 3, r, 3 * r} : Finset ℕ) ⊆ (3 * r).divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Nat.mem_divisors]
    refine ⟨?_, hq⟩
    rcases hx with h | h | h | h <;> subst h
    · exact one_dvd _
    · exact Dvd.intro r rfl
    · exact Dvd.intro_left 3 rfl
    · exact dvd_rfl
  have hsum : ∑ x ∈ ({1, 3, r, 3 * r} : Finset ℕ), x = 4 * r + 4 := by
    rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; omega),
      Finset.sum_singleton]
    omega
  calc 4 * r + 4 = ∑ x ∈ ({1, 3, r, 3 * r} : Finset ℕ), x := hsum.symm
    _ ≤ ∑ x ∈ (3 * r).divisors, x := Finset.sum_le_sum_of_subset hsub
    _ = σ 1 (3 * r) := (ArithmeticFunction.sigma_one_apply _).symm

/-- For odd `p`, the geometric sum `1 + p + ⋯ + p^{t-1}` has the parity of `t`. -/
