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

lemma primeFactors_prod_pow {n : ℕ} {S : Finset ℕ} (hS : S ⊆ n.primeFactors) :
    (∏ p ∈ S, p ^ n.factorization p).primeFactors = S := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hsub : s ⊆ n.primeFactors := fun x hx => hS (mem_insert_of_mem hx)
      have hamem : a ∈ n.primeFactors := hS (mem_insert_self a s)
      have hap : a.Prime := Nat.prime_of_mem_primeFactors hamem
      have hafac : n.factorization a ≠ 0 := by
        have := (Nat.mem_primeFactors.mp hamem)
        simpa [Nat.factorization_eq_zero_iff, hap.ne_one, this.2.2] using
          (Nat.Prime.factorization_pos_of_dvd hap this.2.2 this.2.1).ne'
      have hne : (a ^ n.factorization a) ≠ 0 := pow_ne_zero _ hap.pos.ne'
      have hne2 : (∏ p ∈ s, p ^ n.factorization p) ≠ 0 := by
        refine Finset.prod_ne_zero_iff.mpr ?_
        intro p hp
        exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hsub hp)).pos.ne'
      rw [Finset.prod_insert ha, Nat.primeFactors_mul hne hne2, ih hsub,
        Nat.primeFactors_prime_pow hafac hap]
      simp

