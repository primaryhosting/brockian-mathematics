import Mathlib

/-!
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
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

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-- `Betrothed m n` says that `(m, n)` is a betrothed (quasi-amicable) pair:
both are positive and `σ m = σ n = m + n + 1`. -/

lemma sigma_primePow_le {p : ℕ} (hp : 2 ≤ p) (a : ℕ) :
    ((∑ k ∈ range (a + 1), p ^ k : ℕ) : ℚ) ≤ (p : ℚ) ^ a * primeRatio p := by
  have hp' : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
  have hp1 : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  have hcast : ((∑ k ∈ range (a + 1), p ^ k : ℕ) : ℚ) = ∑ k ∈ range (a + 1), (p : ℚ) ^ k := by
    push_cast; ring
  rw [hcast, geom_sum_eq (by linarith) (a + 1), primeRatio]
  rw [div_le_iff₀ hp1]
  have : (p : ℚ) ^ a * ((p : ℚ) / ((p : ℚ) - 1)) * ((p : ℚ) - 1) = (p : ℚ) ^ (a + 1) := by
    field_simp; ring
  rw [this]
  have : (p : ℚ) ^ (a + 1) - 1 ≤ (p : ℚ) ^ (a + 1) := by linarith
  linarith

/-- **Rational abundancy bound**: `σ n ≤ n * ∏_{p ∣ n} p / (p - 1)`. -/
