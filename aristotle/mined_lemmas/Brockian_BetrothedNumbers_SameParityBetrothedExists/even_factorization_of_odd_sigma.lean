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

-- (The header above uses `/-` rather than `/-!` only because Lean 4 does not allow a module
-- docstring to precede the `import` commands.)

import Mathlib

open Nat ArithmeticFunction

namespace Brockian
namespace BetrothedNumbers

/-- Two positive naturals `m`, `n` are *betrothed* (a quasi-amicable pair) when the sum of the
divisors of each equals `m + n + 1`; equivalently, the sum of the *proper* divisors of each,
excluding `1`, gives the other number. -/

theorem even_factorization_of_odd_sigma {n : ℕ} (hn : n ≠ 0)
    (hodd : Odd (∑ d ∈ n.divisors, d)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Even (n.factorization p) := by
  by_cases hpn : p ∈ n.primeFactors
  · rw [← ArithmeticFunction.sigma_one_apply,
      ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn] at hodd
    set a := n.factorization p with ha
    have hdvd : (∑ i ∈ Finset.range (a + 1), p ^ (i * 1)) ∣
        ∏ q ∈ n.primeFactors, ∑ i ∈ Finset.range (n.factorization q + 1), q ^ (i * 1) :=
      Finset.dvd_prod_of_mem _ hpn
    have hS : Odd (∑ i ∈ Finset.range (a + 1), p ^ (i * 1)) := by
      rcases Nat.even_or_odd (∑ i ∈ Finset.range (a + 1), p ^ (i * 1)) with he | ho
      · exact absurd (even_iff_two_dvd.mpr (dvd_trans (even_iff_two_dvd.mp he) hdvd))
          (Nat.not_even_iff_odd.mpr hodd)
      · exact ho
    have hmod : (∑ i ∈ Finset.range (a + 1), p ^ (i * 1)) % 2 = (a + 1) % 2 := by
      rw [Finset.sum_nat_mod]
      have hone : ∀ i ∈ Finset.range (a + 1), p ^ (i * 1) % 2 = 1 := by
        intro i _
        exact Nat.odd_iff.mp ((hp.odd_of_ne_two hp2).pow)
      rw [Finset.sum_congr rfl hone]
      simp
    rw [Nat.odd_iff, hmod] at hS
    rw [Nat.even_iff]
    omega
  · have hnd : ¬ p ∣ n := fun hd => hpn (Nat.mem_primeFactors.mpr ⟨hp, hd, hn⟩)
    rw [Nat.factorization_eq_zero_of_not_dvd hnd]
    exact even_zero

/-- A squarefree number all of whose prime factors equal `2` is either `1` or `2`. -/
