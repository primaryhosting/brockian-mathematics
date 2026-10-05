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

theorem mem_betrothedSet_iff (n : ℕ) :
    n ∈ betrothedSet ↔
      0 < n ∧ n + 1 < σ 1 n ∧ σ 1 n - n - 1 ≠ n ∧
        σ 1 (σ 1 n - n - 1) = σ 1 n := by
  constructor
  · rintro ⟨m, hn, hmpos, hne, h1, h2⟩
    have hmeq : m = σ 1 n - n - 1 := by omega
    subst hmeq
    exact ⟨hn, by omega, fun h => hne h.symm, by omega⟩
  · rintro ⟨hn, hlt, hne, hσ⟩
    exact ⟨σ 1 n - n - 1, hn, by omega, fun h => hne h.symm, by omega, by omega⟩

/-- Every betrothed number `n` satisfies `σ₁(n) > n + 1`. -/
