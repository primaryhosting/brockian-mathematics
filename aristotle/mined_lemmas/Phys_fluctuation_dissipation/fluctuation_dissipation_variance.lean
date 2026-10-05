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
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

variable {ι : Type*} [Fintype ι]

/-- The Boltzmann weight `exp (-β (E i - λ A i))` of the microstate `i`, for the
Hamiltonian `E` perturbed by the field `λ` coupled to the observable `A`. -/

theorem fluctuation_dissipation_variance [Nonempty ι] (beta : ℝ) (E A : ι → ℝ) :
    HasDerivAt (fun lam => expect beta E A lam A)
      (beta * expect beta E A 0 (fun i => (A i - expect beta E A 0 A) ^ 2)) 0 := by
  have hZ : partition beta E A 0 ≠ 0 := (partition_pos beta E A 0).ne'
  set m : ℝ := expect beta E A 0 A with hm
  have key : expect beta E A 0 (fun i => (A i - m) ^ 2)
      = expect beta E A 0 (fun i => A i ^ 2) - m ^ 2 := by
    have hsum : ∑ i, (A i - m) ^ 2 * boltzmannWeight beta E A 0 i
        = (∑ i, A i ^ 2 * boltzmannWeight beta E A 0 i)
          - 2 * m * (∑ i, A i * boltzmannWeight beta E A 0 i)
          + m ^ 2 * ∑ i, boltzmannWeight beta E A 0 i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hmm : m * partition beta E A 0 = ∑ i, A i * boltzmannWeight beta E A 0 i := by
      rw [hm, expect, div_mul_cancel₀ _ hZ]
    simp only [expect, hsum]
    rw [show (∑ i, boltzmannWeight beta E A 0 i) = partition beta E A 0 from rfl]
    field_simp
    rw [← hmm]; ring
  rw [key]
  exact fluctuation_dissipation beta E A

/-- The equilibrium expectation of a nonnegative observable is nonnegative. -/
