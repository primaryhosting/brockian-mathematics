/-
Franklin's involution and the combinatorial core of Euler's pentagonal number theorem.
-/
import Mathlib

namespace EulerPentagonal

open Finset

/-- The minimum of a finset of naturals (`0` for the empty set). -/

theorem sum_D_eq (n : ℕ) :
    ∑ S ∈ D n, (-1 : ℤ) ^ S.card
      = (∑ c ∈ (Finset.Icc 1 n).filter (fun c => c * (3 * c - 1) = 2 * n), (-1 : ℤ) ^ c)
      + (∑ c ∈ (Finset.Icc 1 n).filter (fun c => c * (3 * c + 1) = 2 * n), (-1 : ℤ) ^ c)
      + (if n = 0 then 1 else 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
    rw [D, h1, Finset.powerset_empty, Finset.filter_singleton, if_pos (by simp)]
    simp
  · rw [if_neg (by omega), add_zero,
      ← Finset.sum_filter_add_sum_filter_not (D n) (fun S => IsExc S),
      sum_nonexc_eq_zero n hn, add_zero, sum_exc n]

end Core

end EulerPentagonal

/-
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
import RequestProject.Franklin

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

namespace Math

open EulerPentagonal

/-- Extracting the `n`-th coefficient of the finite product `∏_{k=1}^{N} (1 - X^k)`:
it is the signed count of the subsets of `{1, …, N}` summing to `n`. -/
