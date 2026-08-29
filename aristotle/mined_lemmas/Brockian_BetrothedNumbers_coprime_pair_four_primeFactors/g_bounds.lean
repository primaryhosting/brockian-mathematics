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

lemma g_bounds {p : ℕ} (hp : p.Prime) :
    1 ≤ (p : ℚ) / ((p : ℚ) - 1) ∧ (p : ℚ) / ((p : ℚ) - 1) ≤ 2 ∧
      (p ≠ 2 → (p : ℚ) / ((p : ℚ) - 1) ≤ 3 / 2) ∧
      (p ≠ 2 → p ≠ 3 → (p : ℚ) / ((p : ℚ) - 1) ≤ 5 / 4) := by
  have h2 := hp.two_le
  have hp2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast h2
  have hpm : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  refine ⟨by rw [le_div_iff₀ hpm]; linarith, by rw [div_le_iff₀ hpm]; linarith, ?_, ?_⟩
  · intro h
    have h3 : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast (by omega : 3 ≤ p)
    rw [div_le_iff₀ hpm]; linarith
  · intro h h3
    have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
    have h5 : (5 : ℚ) ≤ (p : ℚ) := by exact_mod_cast (by omega : 5 ≤ p)
    rw [div_le_iff₀ hpm]; linarith

