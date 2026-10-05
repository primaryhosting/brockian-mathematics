import Mathlib
/-!
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
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

open ArithmeticFunction

/-- A *betrothed* (quasi-amicable) pair: two distinct positive integers `m ≠ n` such that
the sum of the divisors of each equals `m + n + 1`, i.e. each is the sum of the *nontrivial*
divisors (excluding `1` and the number itself) of the other. -/

lemma three_primes_prod_le {a b c : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (a : ℚ) / ((a : ℚ) - 1) * ((b : ℚ) / ((b : ℚ) - 1)) * ((c : ℚ) / ((c : ℚ) - 1)) ≤ 15 / 4 := by
  obtain ⟨ha1, ha2, ha3, ha5⟩ := g_bounds ha
  obtain ⟨hb1, hb2, hb3, hb5⟩ := g_bounds hb
  obtain ⟨hc1, hc2, hc3, hc5⟩ := g_bounds hc
  rcases eq_or_ne a 2 with rfl | ha'
  · rcases eq_or_ne b 3 with rfl | hb'
    · have := prod3_le ha1 hb1 hc1 ha2 (hb3 (by norm_num)) (hc5 (Ne.symm hac) (Ne.symm hbc))
      linarith
    · rcases eq_or_ne c 3 with rfl | hc'
      · have := prod3_le ha1 hb1 hc1 ha2 (hb5 (Ne.symm hab) hb') (hc3 (by norm_num))
        linarith
      · have := prod3_le ha1 hb1 hc1 ha2 (hb5 (Ne.symm hab) hb') (hc5 (Ne.symm hac) hc')
        linarith
  · rcases eq_or_ne b 2 with rfl | hb'
    · rcases eq_or_ne a 3 with rfl | ha''
      · have := prod3_le ha1 hb1 hc1 (ha3 ha') hb2 (hc5 (Ne.symm hbc) (Ne.symm hac))
        linarith
      · have := prod3_le ha1 hb1 hc1 (ha5 ha' ha'') hb2 (hc3 (Ne.symm hbc))
        linarith
    · rcases eq_or_ne c 2 with rfl | hc'
      · rcases eq_or_ne a 3 with rfl | ha''
        · have := prod3_le ha1 hb1 hc1 (ha3 ha') (hb5 hb' (Ne.symm hab)) hc2
          linarith
        · have := prod3_le ha1 hb1 hc1 (ha5 ha' ha'') (hb3 hb') hc2
          linarith
      · have := prod3_le ha1 hb1 hc1 (ha3 ha') (hb3 hb') (hc3 hc')
        linarith

/-- A set of at most three primes has Euler product at most `15/4`. -/
