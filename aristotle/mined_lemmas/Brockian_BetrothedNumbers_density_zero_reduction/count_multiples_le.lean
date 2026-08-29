import Mathlib

/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

open scoped BigOperators
open scoped Classical
open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian
namespace BetrothedNumbers

/-! ## Betrothed (quasi-amicable) numbers -/

/-- `n` and `m` form a *betrothed* (quasi-amicable) pair: they are distinct positive
integers whose sums of divisors both equal `n + m + 1`, i.e. each is the sum of the
proper divisors, excluding `1`, of the other. -/

theorem count_multiples_le (d x : ℕ) (hd : 0 < d) :
    count {n : ℕ | d ∣ n} x ≤ x / d + 1 := by
  unfold count
  refine le_trans (Finset.card_le_card
      (t := (Finset.range (x / d + 1)).image (fun k => d * k)) ?_)
    (le_trans Finset.card_image_le (by simp))
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq] at hn
  obtain ⟨hlt, k, rfl⟩ := hn
  refine Finset.mem_image.2 ⟨k, ?_, rfl⟩
  simp only [Finset.mem_range]
  have h1 : k = d * k / d := by rw [Nat.mul_div_cancel_left _ hd]
  have hk : d * k / d ≤ x / d := Nat.div_le_div_right (le_of_lt hlt)
  omega

/-- The number of perfect squares below `x` is at most `√x + 1`. -/
