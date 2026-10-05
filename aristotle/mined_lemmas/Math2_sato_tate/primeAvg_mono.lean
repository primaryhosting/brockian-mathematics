import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
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

set_option grind.warning false

namespace Math2

open Filter Topology Set Polynomial

/-- The Sato–Tate density `(2/π) sin²θ` on the interval `[0, π]`. -/

lemma primeAvg_mono {θ : ℕ → ℝ} {f g : ℝ → ℝ} {N : ℕ} (hN : 2 ≤ N) (h : ∀ t, f t ≤ g t) :
    primeAvg θ f N ≤ primeAvg θ g N := by
  have hcard : 0 < ((primesUpTo N).card : ℝ) := by exact_mod_cast card_primesUpTo_pos hN
  have hsum : ∑ p ∈ primesUpTo N, f (θ p) ≤ ∑ p ∈ primesUpTo N, g (θ p) :=
    Finset.sum_le_sum fun p _ => h (θ p)
  simp only [primeAvg, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hsum (by positivity)

/-- **Sato–Tate in counting form.**  If the angles are Sato–Tate distributed, then for every
subinterval `[α, β] ⊆ [0, π]` the proportion of primes `p ≤ N` with `θ p ∈ [α, β]` converges
to the Sato–Tate measure `∫_α^β (2/π) sin²t dt` of that interval. -/
