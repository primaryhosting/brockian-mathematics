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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PracticalNumbers

open Finset Pointwise

/-! ## Basic definitions -/

/-- The sum of the (positive) divisors of `n`. -/

lemma covers_mul_prime_pow_succ {n p j : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) (hn : 0 < n)
    (hcov : Covers (n * p ^ j)) (hcovn : Covers n) (hple : p ^ (j + 1) ≤ sigma1 (n * p ^ j) + 1) :
    Covers (n * p ^ (j + 1)) := by
  refine ⟨Nat.mul_pos hn (pow_pos hp.pos _), ?_⟩
  intro k hk
  rw [sigma1_mul_prime_pow_succ hp hpn] at hk
  set c := p ^ (j + 1) with hc
  have hcpos : 0 < c := pow_pos hp.pos _
  set T := sigma1 n with hT
  set t := min T (k / c) with ht
  have htT : t ≤ T := min_le_left _ _
  have hct : c * t ≤ k := by
    calc c * t ≤ c * (k / c) := Nat.mul_le_mul_left _ (min_le_right _ _)
      _ = (k / c) * c := mul_comm _ _
      _ ≤ k := Nat.div_mul_le_self k c
  have hs : k - c * t ≤ sigma1 (n * p ^ j) := by
    rcases le_or_gt T (k / c) with h | h
    · have : t = T := by omega
      rw [this]
      omega
    · have : t = k / c := by omega
      rw [this]
      have hmod : k - c * (k / c) = k % c := by
        have := Nat.div_add_mod k c
        omega
      rw [hmod]
      have : k % c < c := Nat.mod_lt _ hcpos
      omega
  obtain ⟨S₁, hS₁sub, hS₁sum⟩ := hcov.2 (k - c * t) hs
  obtain ⟨S₂, hS₂sub, hS₂sum⟩ := hcovn.2 t htT
  refine ⟨(S₂ * ({c} : Finset ℕ)) ∪ S₁, ?_, ?_⟩
  · rw [divisors_mul_prime_pow_succ hp]
    exact Finset.union_subset_union
      (Finset.mul_subset_mul hS₂sub (Finset.Subset.refl _)) hS₁sub
  · have hdisj : Disjoint (S₂ * ({c} : Finset ℕ)) S₁ :=
      Finset.disjoint_of_subset_left (Finset.mul_subset_mul hS₂sub (Finset.Subset.refl _))
        (Finset.disjoint_of_subset_right hS₁sub (disjoint_divisors_mul_prime_pow hp hpn))
    rw [Finset.sum_union hdisj, sum_mul_singleton hcpos, hS₁sum, hS₂sum]
    omega

