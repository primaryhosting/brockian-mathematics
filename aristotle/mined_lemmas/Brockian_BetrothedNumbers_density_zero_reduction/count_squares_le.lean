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

theorem count_squares_le (x : ℕ) : count {n : ℕ | IsSquare n} x ≤ Nat.sqrt x + 1 := by
  unfold count
  refine le_trans (Finset.card_le_card
      (t := (Finset.range (Nat.sqrt x + 1)).image (fun k => k * k)) ?_)
    (le_trans Finset.card_image_le (by simp))
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq] at hn
  obtain ⟨hlt, r, rfl⟩ := hn
  refine Finset.mem_image.2 ⟨r, ?_, rfl⟩
  simp only [Finset.mem_range]
  have h1 : r ≤ Nat.sqrt (r * r) := by simp
  have h2 : Nat.sqrt (r * r) ≤ Nat.sqrt x := Nat.sqrt_le_sqrt (le_of_lt hlt)
  omega

/-- The set of perfect squares has density zero. -/
