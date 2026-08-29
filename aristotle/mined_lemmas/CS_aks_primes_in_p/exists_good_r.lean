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

import RequestProject.AKS.Algorithm

/-!
# Correctness of the AKS primality test

The main result of this file is `AKS.aksTest_iff_prime`:
the decision procedure `AKS.aksTest` returns `true` exactly on the primes.
-/

namespace AKS

open Polynomial Finset


theorem exists_good_r (n B K : ℕ) (hn : 2 ≤ n) (hB : n < 2 ^ B) (hK : 1 ≤ K) :
    ∃ r, 2 ≤ r ∧ r ≤ 2 * (B * K ^ 2) ∧ ∀ i, 1 ≤ i → i ≤ K → n ^ i % r ≠ 1 := by
  classical
  by_contra hcon
  push_neg at hcon
  set M := B * K ^ 2 with hM
  set P : ℕ := ∏ i ∈ Finset.Icc 1 K, (n ^ i - 1) with hP
  have hPpos : 0 < P := by
    rw [hP]
    refine Finset.prod_pos ?_
    intro i hi
    obtain ⟨hi1, -⟩ := Finset.mem_Icc.1 hi
    have : 2 ≤ n ^ i := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ n ^ i := Nat.pow_le_pow_left hn 1 |>.trans (Nat.pow_le_pow_right (by omega) hi1)
    omega
  -- every `r ∈ [1, 2M]` divides `P`
  have hdvd : ∀ r ∈ Finset.Icc 1 (2 * M), (id r : ℕ) ∣ P := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := Finset.mem_Icc.1 hr
    rcases Nat.lt_or_ge r 2 with hlt | hge
    · have : r = 1 := by omega
      simp [this]
    · obtain ⟨i, hi1, hiK, hieq⟩ := hcon r hge hr2
      have hni : 1 ≤ n ^ i := Nat.one_le_pow _ _ (by omega)
      have hrd : r ∣ n ^ i - 1 := by
        have h1 : n ^ i % r = 1 % r := by
          rw [hieq, Nat.mod_eq_of_lt (by omega)]
        exact (Nat.modEq_iff_dvd' hni).1 (Nat.ModEq.symm h1)
      refine dvd_trans hrd ?_
      rw [hP]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_Icc.2 ⟨hi1, hiK⟩)
  have hlcm : lcmUpTo (2 * M) ∣ P := Finset.lcm_dvd hdvd
  have h1 : 2 ^ M ≤ P := le_trans (two_pow_le_lcmUpTo M) (Nat.le_of_dvd hPpos hlcm)
  -- but `P` is small
  have h2 : P ≤ n ^ (K * K) := by
    calc P ≤ ∏ i ∈ Finset.Icc 1 K, n ^ i := by
          refine Finset.prod_le_prod' ?_
          intro i _
          omega
      _ = n ^ (∑ i ∈ Finset.Icc 1 K, i) := by rw [Finset.prod_pow_eq_pow_sum]
      _ ≤ n ^ (K * K) := by
          refine Nat.pow_le_pow_right (by omega) ?_
          calc (∑ i ∈ Finset.Icc 1 K, i) ≤ ∑ _i ∈ Finset.Icc 1 K, K := by
                refine Finset.sum_le_sum ?_
                intro i hi
                exact (Finset.mem_Icc.1 hi).2
            _ = (Finset.Icc 1 K).card * K := by rw [Finset.sum_const, smul_eq_mul]
            _ ≤ K * K := by
                have hcard : (Finset.Icc 1 K).card = K := by rw [Nat.card_Icc]; omega
                rw [hcard]
  have h3 : n ^ (K * K) < 2 ^ M := by
    calc n ^ (K * K) < (2 ^ B) ^ (K * K) := Nat.pow_lt_pow_left hB (by positivity)
      _ = 2 ^ (B * (K * K)) := by rw [← pow_mul]
      _ = 2 ^ M := by rw [hM]; congr 1; ring
  omega

end AKS

import RequestProject.AKS.Introspective

/-!
# Polynomials modulo `X ^ r - 1` represented by coefficient lists

The AKS algorithm computes with polynomials in `(ZMod n)[X] / (X ^ r - 1)`.  Here we represent
such a polynomial by the list of its `r` coefficients (natural numbers `< n`) and give the
schoolbook implementations of multiplication and of binary exponentiation, together with proofs
that they implement the intended ring operations.
-/

namespace AKS

open Polynomial Finset

/-! ## Congruence modulo `X ^ r - 1` -/

/-- `Cong r f g` means `f ≡ g` modulo `X ^ r - 1`. -/
