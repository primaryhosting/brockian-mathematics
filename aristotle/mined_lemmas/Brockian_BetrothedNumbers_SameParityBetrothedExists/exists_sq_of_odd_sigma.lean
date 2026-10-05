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
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace BetrothedNumbers

open Finset

/-- `Betrothed m n` says that `m` and `n` are a pair of *betrothed*
(quasi-amicable) numbers: two distinct positive integers each of whose sum of
divisors equals `m + n + 1`. -/

theorem exists_sq_of_odd_sigma {n : ℕ} (hn : n ≠ 0)
    (h : Odd (∑ d ∈ n.divisors, d)) : ∃ k, n = k ^ 2 ∨ n = 2 * k ^ 2 := by
  -- every odd prime occurs to an even power
  have key : ∀ p : ℕ, p.Prime → p ≠ 2 → Even (n.factorization p) := by
    intro p hp hp2
    by_contra hodd
    have hmem : p ∈ n.primeFactors := by
      rw [Nat.mem_primeFactors]
      refine ⟨hp, ?_, hn⟩
      by_contra hdvd
      exact hodd (by simp [Nat.factorization_eq_zero_of_not_dvd hdvd])
    have hdvd : (∑ k ∈ Finset.range (n.factorization p + 1), p ^ k) ∣
        ∏ q ∈ n.primeFactors, ∑ k ∈ Finset.range (n.factorization q + 1), q ^ k :=
      Finset.dvd_prod_of_mem _ hmem
    rw [← Nat.sum_divisors hn] at hdvd
    have heven : 2 ∣ (∑ k ∈ Finset.range (n.factorization p + 1), p ^ k) := by
      have h1 := geom_sum_mod_two (p := p) (hp.odd_of_ne_two hp2) (n.factorization p + 1)
      have h2 : (n.factorization p + 1) % 2 = 0 := by
        rcases Nat.even_or_odd (n.factorization p) with he | ho
        · exact absurd he hodd
        · rw [Nat.odd_iff] at ho; omega
      omega
    have hdvd2 : 2 ∣ ∑ d ∈ n.divisors, d := heven.trans hdvd
    rw [Nat.odd_iff] at h
    omega
  set a := n.factorization 2 with ha
  set m := n / 2 ^ a with hmdef
  have hmn : 2 ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hm0 : m ≠ 0 := (Nat.ordCompl_pos 2 hn).ne'
  have hmfac : ∀ p, Even (m.factorization p) := by
    intro p
    rw [hmdef, ha, Nat.factorization_ordCompl]
    by_cases hp2 : p = 2
    · simp [hp2]
    · rw [Finsupp.erase_ne hp2]
      by_cases hp : p.Prime
      · exact key p hp hp2
      · simp [Nat.factorization_eq_zero_of_not_prime n hp]
  obtain ⟨k, hk⟩ := isSquare_of_even_factorization hm0 hmfac
  rcases Nat.even_or_odd a with ⟨b, hb⟩ | ⟨b, hb⟩
  · refine ⟨2 ^ b * k, Or.inl ?_⟩
    rw [← hmn, hk, hb]
    ring
  · refine ⟨2 ^ b * k, Or.inr ?_⟩
    rw [← hmn, hk, hb]
    ring

/-- Necessary condition: in a betrothed pair whose members have the same
parity, each member is a perfect square or twice a perfect square.  (For such a
pair the common divisor sum `m + n + 1` is odd.) -/
