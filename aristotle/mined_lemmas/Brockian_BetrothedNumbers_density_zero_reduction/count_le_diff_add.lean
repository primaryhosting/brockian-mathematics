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

theorem count_le_diff_add (A B : Set ℕ) (x : ℕ) :
    count A x ≤ count B x + count (A \ B) x := by
  calc count A x ≤ count (B ∪ (A \ B)) x := count_mono (fun n hn => by
        by_cases h : n ∈ B
        · exact Or.inl h
        · exact Or.inr ⟨hn, h⟩) x
    _ ≤ _ := count_union_le _ _ x

/-- Criterion for density zero: for every `ε > 0` the counting function is eventually
at most `ε x`. -/
