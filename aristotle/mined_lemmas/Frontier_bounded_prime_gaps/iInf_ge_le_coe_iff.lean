import Mathlib

/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
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

namespace Frontier

open Filter

/-- `primeGap n = p_{n+1} - p_n`, where `p_n = Nat.nth Nat.Prime n` is the `n`-th prime
(with `p_0 = 2`). -/

lemma iInf_ge_le_coe_iff (f : ℕ → ℕ∞) (N B : ℕ) :
    (⨅ i ≥ N, f i) ≤ (B : ℕ∞) ↔ ∃ i ≥ N, f i ≤ (B : ℕ∞) := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hle : ((B : ℕ∞) + 1) ≤ ⨅ i ≥ N, f i := by
      refine le_iInf fun i => le_iInf fun hi => ?_
      exact Order.add_one_le_of_lt (hc i hi)
    have hBB : ((B : ℕ∞) + 1) ≤ (B : ℕ∞) := hle.trans h
    have h2 : ((B + 1 : ℕ) : ℕ∞) ≤ ((B : ℕ) : ℕ∞) := by push_cast; exact hBB
    have h3 : B + 1 ≤ B := Nat.cast_le.mp h2
    omega
  · rintro ⟨i, hi, hle⟩
    exact le_trans (iInf_le_of_le i (iInf_le_of_le hi le_rfl)) hle

/-- In `ℕ∞`, a supremum is finite iff it is bounded by a natural number. -/
