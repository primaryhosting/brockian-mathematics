/-
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

open Finset

/-! ## Basic definitions -/

/-- `sigmaOne n` is the sum-of-divisors function `σ₁(n) = ∑_{d ∣ n} d`. -/

lemma w_anti {a c : ℕ} (ha : 2 ≤ a) (hac : a ≤ c) : w c ≤ w a := by
  have h2 : (2:ℚ) ≤ (a:ℚ) := by exact_mod_cast ha
  have h3 : (a:ℚ) ≤ (c:ℚ) := by exact_mod_cast hac
  unfold w
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

