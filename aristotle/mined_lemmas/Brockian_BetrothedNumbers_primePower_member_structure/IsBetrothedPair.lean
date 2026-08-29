import Mathlib

/-!
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction Finset

namespace Brockian
namespace BetrothedNumbers

/-- `IsBetrothedPair m n` says that `(m, n)` is a betrothed (quasi-amicable) pair: two distinct
positive integers, each of whose sum of divisors equals `m + n + 1`. -/

theorem IsBetrothedPair.symm {m n : ℕ} (h : IsBetrothedPair m n) : IsBetrothedPair n m := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h2, h1, h3.symm, ?_, ?_⟩
  · rw [h5]; ring
  · rw [h4]; ring

/-- The smallest betrothed pair; in particular the definition is not vacuous. -/
