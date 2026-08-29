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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.UnitaryPerfect

open Finset

/-- `d` is a *unitary divisor* of `n` if `d ∣ n` and `d` is coprime to `n / d`. -/

lemma usigma_eq_prod {n : ℕ} (hn : n ≠ 0) :
    usigma n = ∏ p ∈ n.primeFactors, (p ^ n.factorization p + 1) := by
  have hinj : Set.InjOn (fun S => ∏ p ∈ S, p ^ n.factorization p)
      (↑n.primeFactors.powerset : Set (Finset ℕ)) := by
    intro S hS T hT h
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff] at hS hT
    have hS' : S ⊆ n.primeFactors := by
      intro x hx
      have := hS (by simpa using hx)
      simpa using this
    have hT' : T ⊆ n.primeFactors := by
      intro x hx
      have := hT (by simpa using hx)
      simpa using this
    rw [← primeFactors_prod_pow hS', ← primeFactors_prod_pow hT']
    exact congrArg Nat.primeFactors h
  rw [usigma, unitaryDivisors_eq_image hn, Finset.sum_image hinj]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  simp

