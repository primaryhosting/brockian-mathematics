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

/-! ## Unitary divisors and the unitary divisor sum -/

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd d (n / d) = 1`. -/

theorem usigma_list_prod :
    ∀ (l : List ℕ), (∀ x ∈ l, ∃ p k, Nat.Prime p ∧ 0 < k ∧ x = p ^ k) →
      l.Pairwise Nat.Coprime → usigma l.prod = (l.map (fun x => 1 + x)).prod
  | [], _, _ => by simpa using usigma_one
  | a :: l, hpp, hc => by
      obtain ⟨p, k, hp, hk, rfl⟩ := hpp a (by simp)
      have hane : p ^ k ≠ 0 := pow_ne_zero _ hp.pos.ne'
      have hlne : l.prod ≠ 0 := by
        refine List.prod_ne_zero ?_
        intro h0
        obtain ⟨q, j, hq, _, hqj⟩ := hpp 0 (by simp [h0])
        exact pow_ne_zero _ hq.pos.ne' hqj.symm
      have hcop : Nat.Coprime (p ^ k) l.prod :=
        coprime_list_prod l fun b hb => (List.pairwise_cons.1 hc).1 b hb
      rw [List.prod_cons, usigma_mul_of_coprime hane hlne hcop, usigma_prime_pow hp hk,
        usigma_list_prod l (fun x hx => hpp x (by simp [hx])) (List.pairwise_cons.1 hc).2]
      simp

/-! ## The five known unitary perfect numbers -/

